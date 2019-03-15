module BackEnd.DeadCode where
import BackEnd.Canon
import BackEnd.Translate as Translate
import BackEnd.IR as IR
import Control.Monad.State.Lazy
import BackEnd.Frame
import Data.Maybe
import Data.List
import BackEnd.Temp as Temp
import FrontEnd.AST
import FrontEnd.Parser
import FrontEnd.SemanticAnalyzer
import BackEnd.DataFlow hiding (addreTree, contains)

type PredTable = [(Int, [Int])]
type SuccTable = [(Int, [Int])]
type L = [(Int, ([Exp], [Exp]))]
type SynTable = [(Exp, Int)]
type EqualTable = [(Exp, Exp)]
data LFlow = L {    tree :: Stm,
                    defid :: Int,
                    reTree :: [Stm]}
                    deriving (Show, Eq)

data LState = LState {  idCount :: Int,
                        memFlow :: [Exp],
                        wrappedFlow :: [LFlow],
                        synExpr :: SynTable,
                        st :: SuccTable,
                        pt :: PredTable,
                        lock :: [Int],
                        et :: EqualTable} deriving (Show, Eq)

newLState = LState {idCount = 0, memFlow = [], wrappedFlow = [],
                    st = [], pt = [], lock = [], et = [], synExpr = []} 

newL :: Stm -> State LState LFlow
newL t = do
    oldState <- get
    let count = idCount oldState
    put $ oldState {idCount = count + 1}
    return $ L {defid = count, tree = t, reTree = []}

wrapL :: [Stm] -> State LState [LFlow]
wrapL stms = do
    flows <- mapM addOneL stms
    state <- get
    put $ state {wrappedFlow = flows}
    return flows

-- wrap stm with LFlow but WITHOUT gen/kill
addOneL :: Stm -> State LState LFlow
addOneL s = newL s

genLSucc :: [LFlow] -> SuccTable
genLSucc flow = genLSucc' flow flow []

genLSucc' :: [LFlow] -> [LFlow] -> SuccTable -> SuccTable
genLSucc' src [] acc = acc
genLSucc' src ((L (CJUMP _ _ _ t f) defid _) : rest) acc
    = genLSucc' src rest (acc ++ [(defid, (searchLable t src) ++ (searchLable f src))])
genLSucc' src ((L (JUMP (NAME l) _) defid _) : rest) acc
    = genLSucc' src rest (acc ++ [(defid, (searchLable l src))])
genLSucc' src ((L _ defid _) : rest) acc
    = genLSucc' src rest (acc ++ [(defid, (nextID defid src))])

genLPred :: [LFlow] -> PredTable
genLPred flow = genLPred' flow flow []

genLPred' :: [LFlow] -> [LFlow] -> PredTable -> PredTable
genLPred' src [] acc = acc
genLPred' src ((L (LABEL l) defid _) : rest) acc = genLPred' src rest (acc ++ [(defid, (searchLable l))])
    where
        searchLable :: String -> [Int]
        searchLable l = (searchLable' src l []) ++ pred
        searchLable' :: [LFlow] -> String -> [Int] -> [Int]
        searchLable' [] _ acc = acc
        searchLable' ((L (JUMP _ lables) defid _) : rest) l acc
            | elem l lables = searchLable' rest l (defid:acc)
        searchLable' ((L (CJUMP _ _ _ t f) defid _) : rest) l acc
            | l == t || l == f = searchLable' rest l (defid:acc)
        searchLable' (_:rest) l acc = searchLable' rest l acc
        pred = if (defid /= 0)&&(isNotjump (src!! (defid - 1)))
                then (prevId defid) else []
        isNotjump (L (JUMP _ _) _ _) = False
        isNotjump (L (CJUMP _ _ _ _ _) _ _) = False
        isNotjump _ = True

genLPred' src ((L _ defid _) : rest) acc = genLPred' src rest (acc ++ [(defid, (prevId defid))])

searchLable :: String -> [LFlow] -> [Int]
searchLable str ((L (LABEL lab) defid _):xs)
    | str == lab = defid : (searchLable str xs)
searchLable str (x:xs) = searchLable str xs
searchLable _ [] = []

nextID x src
    | x < (length src - 1) = [x + 1]
    | otherwise = []

genEqual :: State LState ()
genEqual = do
    state <- get
    mapM (addEqual) (wrappedFlow state)
    return ()

addEqual :: LFlow -> State LState ()
addEqual flow = do
    case tree flow of
        (MOV a b) -> if not (containsSP a || containsSP b) then 
                        updateEqual (a, b)
                     else return ()
        otherwise -> return ()

containsSP :: Exp -> Bool
containsSP (TEMP 13) = True
containsSP (TEMP 0) = True
containsSP (TEMP 1) = True
containsSP (TEMP 2) = True
containsSP (BINEXP _ a b) = containsSP a || containsSP b
containsSP (MEM a _) = containsSP a
containsSP _ = False

updateEqual :: (Exp, Exp) -> State LState ()
updateEqual (a, b) = do
    state <- get
    put $ state {et = ((a, b) : (b, a) : (et state))}
    return ()

eliminateDeadCode :: [Stm] -> State LState [Stm]
eliminateDeadCode stms = do
    state <- get
    let (flows, wrappedState) = runState (wrapL stms) state
        succ = genLSucc flows
        pred = genLPred flows
        hasMalloc = containsMalloc stms
    if hasMalloc then
        return stms
    else do
        put $ wrappedState {st = succ, pt = pred}
        -- put everything in the state
        mapM (addreTree) (wrappedFlow wrappedState)
        --    genEqual
        --    genSym
        recursiveElim
        clearDeadCode
        state' <- get
        return $ clearStack $ unL $ wrappedFlow state'

containsMalloc :: [Stm] -> Bool
containsMalloc ((EXP (CALL (NAME "malloc") _)) : xs) = True
containsMalloc (x:xs) = containsMalloc xs
containsMalloc [] = False

addreTree :: LFlow -> State LState ()
addreTree flow = do
    -- add the tree_ to reTree_, put it back to the state and return
    updateLFlow $ flow {reTree = [tree flow]}

updateLFlow :: LFlow -> State LState ()
updateLFlow flow = do
    state <- get
    let flows = wrappedFlow state
        defid_ = defid flow
        (prev, aft) = splitAt defid_ flows
    put $ state {wrappedFlow = prev ++ [flow] ++ (drop 1 aft)}
    return ()

unL :: [LFlow] -> [Stm]
unL flows = concatMap reTree flows

recursiveElim :: State LState ()
recursiveElim = do
    state <- get
    elimAll
    state' <- get
    let oldLock = lock state
        newLock = lock state'
    if length oldLock == length newLock then
        return ()
    else
        recursiveElim

elimAll :: State LState ()
elimAll = do
    state <- get
    mapM elimOne [0..(length (wrappedFlow state) - 1)]
    state' <- get
    let locks = lock state'
    put state' {lock = sort $ nub $ locks}
    return ()

elimOne :: Int -> State LState ()
elimOne targetNum = do
    state <- get
    let flows = (wrappedFlow state)
        targetFlow = flows !! targetNum
        locks = lock state
    if (not $ sideEffect targetFlow) && (not $ elem targetNum locks) then
        return ()
    else
        lockUsed targetFlow >>
        lockFlow targetFlow

lockFlow :: LFlow -> State LState ()
lockFlow flow = do
    state <- get
    let locks = lock state
    put $ state {lock = (defid flow : locks)}
    return ()

notSpecial t = not $ elem t [0, 1, 2, 13, 14, 15]

lockEqualMem :: Exp -> LFlow -> State LState ()
lockEqualMem m@(MEM a size) flow = do
    state <- get
    let syn = lookup (MEM a size) (synExpr state) 
        pt_ = pt state
    case syn of
        Just num -> lockSynonym num (defid flow) pt_
        Nothing -> return ()

lockEqualMem m flow = lockEqualMem (MEM m 1) flow >> lockEqualMem (MEM m 4) flow

lockSynonym :: Int -> Int -> PredTable -> State LState ()
lockSynonym synNum cur pt= do
    let next' = Data.List.lookup cur pt
    case next' of
        Nothing -> return ()
        Just next -> mapM (\x -> lockSynonym' synNum x pt [cur]) (next) >>
                    return ()

lockSynonym' :: Int -> Int -> PredTable -> [Int] -> State LState ()
lockSynonym' synNum cur pt visited = do
    state <- get
    let flow = (wrappedFlow state) !! cur
        et_ = et state
    found <- startswithSyn (tree flow) synNum
    if found then do
        lockFlow flow
    else do
        let next' = Data.List.lookup cur pt
        case next' of
            Nothing -> return ()
            Just next -> mapM (\x -> lockSynonym' synNum x pt (cur:visited)) (next \\ visited) >>
                        return ()

startswithSyn :: Stm -> Int -> State LState Bool
startswithSyn (MOV a _) target= do
    state <- get
    let table = synExpr state
    case (lookup a table) of
        Nothing -> return False
        Just a' -> return $ a' == target
startswithSyn (EXP (CALL (NAME "malloc") [_, t])) target = do
    state <- get
    let table = synExpr state
    case (lookup t table) of
        Nothing -> return False
        Just t' -> return $ t' == target
startswithSyn _ _ = return False

genSym :: State LState ()
genSym = do
    state <- get
    let oneL = group1LayerPotential et_ []
        et_ = et state
        multed = addMult oneL et_ 0
        classes = mergeGroups multed et_ 0
        numberclass = zip [0..] classes
    mapM putNumberClass numberclass
    return ()

putNumberClass :: (Int, [Exp]) -> State LState ()
putNumberClass (i, exps) = do
    state <- get
    let synTab = synExpr state
        newSyn = zip exps (repeat i)
    put $ state {synExpr = union newSyn synTab}
    return ()    
    
addMult :: [[Exp]] -> EqualTable -> Int -> [[Exp]]
addMult this et i
    | thislen == nextlen || i > 2 = next
    | otherwise = addMult next et (i + 1)
    where
        thislen = sum (map length this)
        nextlen = sum (map length next)
        next = addMultOne this [] et

addMultOne :: [[Exp]] -> [[Exp]] -> EqualTable -> [[Exp]]
addMultOne [] acc et = acc
addMultOne (thisGroup:remain) acc et = addMultOne remain (newthis:acc) et
    where
        multi = nub $ concatMap (permutateExp (thisGroup:(remain ++ acc))) thisGroup
        newthis = union multi thisGroup

mergeGroups :: [[Exp]] -> EqualTable -> Int -> [[Exp]]
mergeGroups this et i
    | (length this) == (length next) || i > maximum = this
    | otherwise = mergeGroups next et (i + 1)
        where
            next = mergeGroupOne this [] et
            maximum = log_ (length et)
            log_ x = if (odd x) then 0 else (floor . logBase 2.0 . fromIntegral) x 

-- Detect and 'substitute' innterTemps
mergeGroupOne :: [[Exp]] -> [[Exp]] -> EqualTable -> [[Exp]]
mergeGroupOne [] b et = b
mergeGroupOne a@(thisGroup : remain) b et
    = mergeGroupOne remain (newGroup : db) et
        where
            (sremain, dremain) = partition (containsSame thisGroup) remain
            (sb, db) = partition (containsSame thisGroup) b
            tomerge = union (concat sb) (concat sremain)
            newGroup = union tomerge thisGroup

containsSame :: [Exp] -> [Exp] -> Bool
containsSame [] b = False
containsSame (a:as) b = (or (map (same a) b)) || containsSame as b            

group1LayerPotential :: EqualTable -> [[Exp]] -> [[Exp]]
group1LayerPotential [] acc = acc
group1LayerPotential et@((a, b) : xs) acc = group1LayerPotential newEt (newGroup : acc)
    where
        newGroup = genPotential et a [a, b]
        newEt = [(x, y) | (x, y) <- et, not (elem x newGroup)]

genPotential :: EqualTable -> Exp -> [Exp] -> [Exp]
genPotential et x acc
    | newP == [] = acc
    | otherwise = nub $ concatMap (\x -> genPotential et x (acc ++ newP)) newP
    where
        allP = [ y | (x', y) <- et, same x x']
        newP = filter (\x -> not $ elem x acc) allP

--              groupTable
permutateExp :: [[Exp]]-> Exp -> [Exp] 

permutateExp gt (MEM (TEMP t) size) = map (\x -> (MEM x size)) (potential)
    where
        potential = (findSynGroup (TEMP t) gt) 

permutateExp gt (BINEXP rop (TEMP t1) (TEMP t2)) = map (\(x1, x2) -> (BINEXP rop x1 x2)) final
    where
        potential1 = findSynGroup (TEMP t1) gt 
        potential2 = findSynGroup (TEMP t2) gt
        permTwo = concatMap (\x-> zip (repeat x) potential2) potential1
                 ++ concatMap (\x-> zip (repeat x) potential1) potential2
        final = nub permTwo

permutateExp gt (BINEXP rop (TEMP t) a) = map (\x -> (BINEXP rop x a)) potential
    where 
        potential = findSynGroup (TEMP t) gt

permutateExp gt (BINEXP rop a (TEMP t)) = map (\x -> (BINEXP rop a x)) potential
    where
        potential = findSynGroup (TEMP t) gt

permutateExp gt (MEM (MEM (TEMP t) size2) size) = map (\x -> (MEM x size)) (potential)
    where
        potential = (findSynGroup (MEM (TEMP t) size2) gt)

permutateExp _ x = [x]

findSynGroup exp gt =  concat [ x |x <- gt, elem exp x]

same :: Exp -> Exp -> Bool
same (MEM (CALL (NAME "#memaccess") [CONSTI i11, CONSTI i12]) s1) (MEM (CALL (NAME "#memaccess") [CONSTI i21, CONSTI i22]) s2) 
    = (i11 -i12) == (i21 - i22) && s1 == s2
same (MEM a s1) (MEM b s2) = same a b && s1 == s2
same (BINEXP _ a1 b1) (BINEXP _ a2 b2) = (same a1 a1) && (same b1 b2)
same exp1 exp2 = exp1 == exp2

lockUsed :: LFlow -> State LState ()
lockUsed l@(L (EXP m@(CALL (NAME n) _ )) _ _)
    | n == "#memaccess" = getLocks [m] l

lockUsed l@(L (EXP c@(CALL _ exps )) defid _) = getExprLocks exps l

lockUsed l@(L (MOV m@(MEM a size) b@(MEM c size')) defid _) = getExprLocks [a, b, c, m] l 

lockUsed l@(L (MOV m@(MEM (CALL (NAME n) _) _) b) defid _)
    | n == "#memaccess" = getLocks [m, b] l 

lockUsed l@(L (MOV b m@(MEM (CALL (NAME n) _) _)) defid _)
    | n == "#memaccess" = getLocks [m] l 
        
lockUsed l@(L (MOV m@(MEM (TEMP t) size) b) defid _) = getExprLocks [b, (TEMP t)] l 
lockUsed l@(L (MOV m@(MEM a _) b) defid _) = getExprLocks [a, b] l 

lockUsed l@(L (MOV (TEMP t) m@(MEM _ _)) defid _) = getExprLocks [m] l

lockUsed l@(L (MOV (TEMP t) m) defid _) = getExprLocks [m] l

lockUsed l@(L (CJUMP rop a b t f) defid _) = getExprLocks [a, b] l >> lockLable [t, f]

lockUsed l@(L (JUMP _ ns) defid _) = lockLable ns

lockUsed _ = return ()

getExprLocks :: [Exp] -> LFlow -> State LState ()
getExprLocks exps l 
    = mapM (\x -> getExprLocks' x l) exps >> 
--      mapM (\x -> lockEqualMem x l) exps >>
      return ()

getExprLocks' :: Exp -> LFlow -> State LState ()
getExprLocks' (BINEXP bop a b) l = getExprLocks' a l>> getExprLocks' b l
getExprLocks' t@(TEMP _) l = getLocks [t] l
getExprLocks' (CALL _ exps) l = getExprLocks exps l
getExprLocks' (MEM a _) l = getExprLocks' a l
getExprLocks' _ _= return ()

lockLable :: [String] -> State LState ()
lockLable labels = do
    state <- get
    let locks = lock state
        flows = wrappedFlow state
        lablelocks = map defid $ filter (containsLable labels) flows
    put $ state {lock = union locks lablelocks}
    return ()

containsLable :: [String] -> LFlow -> Bool
containsLable labels l@(L (LABEL lab) defid _) = elem lab labels
containsLable _ _ = False

getLocks :: [Exp] -> LFlow -> State LState ()
getLocks exps flow = do
    state <- get
    let pt_ = pt state
        defid_ = defid flow
        flows = wrappedFlow state
        str = concatMap (\m -> findDec m defid_ pt_ flows) exps
    put $ state {lock = (str ++ (lock state))}
    return ()

findDec :: Exp -> Int -> PredTable -> [LFlow] -> [Int]
findDec dec cur pt flows = findDec' dec cur pt flows []

findDec' :: Exp -> Int -> PredTable -> [LFlow] -> [Int] -> [Int]
findDec' dec cur pt flows visited
    | found = [cur]
    | otherwise = concatMap (\x -> findDec' dec x pt flows (cur : visited)) next
    where
        found = startswith (tree (flows !! cur)) dec
        next = (fromJust $ Data.List.lookup cur pt) \\ visited

startswith :: Stm -> Exp -> Bool
startswith (MOV (MEM (CALL (NAME "#memaccess") [CONSTI i11, CONSTI i12]) _) _)
            (MEM (CALL (NAME "#memaccess") [CONSTI i21, CONSTI i22]) _)
    = (i11 -i12) == (i21 - i22)
startswith (MOV a _) target = a == target
startswith (EXP (CALL (NAME "malloc") [_, t])) target = t == target
startswith _ _ = False


clearStack :: [Stm] -> [Stm]
clearStack stms = reverse (clearStack' (reverse stms))

clearStack' ((MOV (TEMP 13) (BINEXP PLUS (TEMP 13) (CONSTI i1))): (MOV (TEMP 13) (BINEXP MINUS (TEMP 13) (CONSTI i2))): xs)
  = clearStack' ((MOV (TEMP 13) (BINEXP PLUS (TEMP 13) (CONSTI $ i1 - i2))):xs)
clearStack' ((MOV (TEMP 13) (BINEXP PLUS (TEMP 13) (CONSTI i1))): (MOV (TEMP 13) (BINEXP PLUS (TEMP 13) (CONSTI i2))): xs)
  = clearStack' ((MOV (TEMP 13) (BINEXP PLUS (TEMP 13) (CONSTI $ i1 + i2))):xs)
clearStack' ((MOV (TEMP 13) (BINEXP MINUS (TEMP 13) (CONSTI i1))): (MOV (TEMP 13) (BINEXP MINUS (TEMP 13) (CONSTI i2))): xs)
    = clearStack' ((MOV (TEMP 13) (BINEXP MINUS (TEMP 13) (CONSTI $ i1 + i2))):xs)
clearStack' (x:xs)
  = x : clearStack' (xs)
clearStack'[] = []

clearDeadCode :: State LState ()
clearDeadCode =  do
    state <- get
    mapM (clearOne (lock state)) (wrappedFlow state)
    return ()

clearOne :: [Int] -> LFlow -> State LState ()
clearOne locks flow
    | (not $ elem (defid flow) locks) && (not $ isFuncLab (tree flow))= updateLFlow $ flow {reTree = []}
    | otherwise = return ()

isFuncLab :: Stm -> Bool
isFuncLab (LABEL n) = not $ "label_" `isPrefixOf` n
isFuncLab _ = False

sideEffect :: LFlow -> Bool
sideEffect l@(L (MOV (MEM _ _) (MEM _ _)) _ _) = True
sideEffect l@(L (MOV (TEMP t) _) _ _)
    | not $ notSpecial t = True
sideEffect l@(L (MOV t (CALL (NAME n) exps)) _ _)
    | "#p_" `isPrefixOf` n || n == "exit" = True
sideEffect l@(L (CJUMP _ a b _ _ ) _ _) = True
sideEffect l@(L (JUMP _ _ ) _ _) = True
sideEffect l@(L (EXP (CALL (NAME n) exps)) _ _)
    | "#p_" `isPrefixOf` n || n == "exit" = True
sideEffect l@(L (LABEL "main" ) _ _) = True
sideEffect l@(L (PUSHREGS _) _ _)  = True
sideEffect l@(L (POPREGS _) _ _)  = True
sideEffect x = False

testDeadCode file = do
    ast <- parseFile file
    ast' <- analyzeAST ast
    let (stm, s) = runState (translate ast') newTranslateState;
        (stms, s') = runState (quadInterface stm) s
        liveCode = evalState (eliminateDeadCode stms) newLState
    return liveCode

testMalloc file = do
    ast <- parseFile file
    ast' <- analyzeAST ast
    let (stm, s) = runState (translate ast') newTranslateState;
        (qstm, qs') = runState (quadInterface stm) s
        (liveCode, livestate) = runState (eliminateDeadCode qstm) newLState
    return $ (synExpr livestate) 


testStms file = do
    ast <- parseFile file
    ast' <- analyzeAST ast
    let (stm, s) = runState (translate ast') newTranslateState;
        (qstm, qs') = runState (quadInterface stm) s
        -- (liveCode, livestate) = runState (eliminateDeadCode stms) newLState
    return $ zip qstm [0..]

testStm = [(MOV (TEMP 2) (CONSTI 2)),(MOV (TEMP 1) (CONSTI 1)) ,(EXP (CALL (NAME "exit") [(TEMP 1)]))]
