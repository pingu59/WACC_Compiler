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
--              deftid mallocId
type EqualTable = [(Exp, Exp)]
data LFlow = L {    tree :: Stm,
                    defid :: Int,
                    reTree :: [Stm]} 
                    deriving (Show, Eq)

data LState = LState {  idCount :: Int,
                        memFlow :: [Exp], 
                        wrappedFlow :: [LFlow],
                        st :: SuccTable,
                        pt :: PredTable,
                        lock :: [Int],
                        et :: EqualTable } deriving (Show, Eq)

newLState = LState {idCount = 0, memFlow = [], wrappedFlow = [],
                    st = [], pt = [], lock = [], et = []} 

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
        (MOV a b) -> updateEqual (a, b)
        otherwise -> return ()

updateEqual :: (Exp, Exp) -> State LState ()
updateEqual pair = do
    state <- get
    put $ state {et = (pair: (et state))}
    return ()

eliminateDeadCode :: [Stm] -> State LState [Stm]
eliminateDeadCode stms = do
    state <- get
    let (flows, wrappedState) = runState (wrapL stms) state
        succ = genLSucc flows
        pred = genLPred flows
    put $ wrappedState {st = succ, pt = pred} 
    -- -- put everything in the state
    genEqual
    mapM (addreTree) (wrappedFlow wrappedState)
    recursiveElim
    clearDeadCode
    state' <- get
    return $ clearStack $ unL $ wrappedFlow state'

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
    if oldLock == newLock then
        return ()
    else
        recursiveElim
    
elimAll :: State LState ()
elimAll = do
    state <- get
    mapM elimOne [0..(length (wrappedFlow state) - 1)]
    state' <- get
    let locks = lock state'
    put state {lock = sort $ nub $ locks}
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

lockUsed :: LFlow -> State LState ()
lockUsed l@(L (EXP m@(CALL (NAME n) _ )) _ _) 
    | n == "#memaccess" = getLocks [m] l

lockUsed l@(L (EXP c@(CALL _ exps )) defid _) = getExprLocks exps l

lockUsed l@(L (MOV m@(MEM (CALL (NAME n) _) _) b) defid _)
    | n == "#memaccess" = getLocks [m, b] l

lockUsed l@(L (MOV b m@(MEM (CALL (NAME n) _) _)) defid _)
    | n == "#memaccess" = getLocks [m] l

lockUsed l@(L (MOV (MEM (TEMP t) size) b) defid _) = getExprLocks [b] l

lockUsed l@(L (MOV (MEM a _) b) defid _) = getExprLocks [a, b] l

lockUsed l@(L (MOV (TEMP t) m) defid _) = getExprLocks [m] l 

lockUsed l@(L (CJUMP rop a b t f) defid _) =  getExprLocks [a, b] l >> lockLable [t, f]

lockUsed l@(L (JUMP _ ns) defid _) = lockLable ns

lockUsed _ = return ()

genMallocTable :: State LState ()
genMallocTable = undefined

getExprLocks :: [Exp] -> LFlow -> State LState ()
getExprLocks exps l = mapM (\x -> getExprLocks' x l) exps >> return ()

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
        (qstm, qs') = runState (quadStm stm) s
        (stms, s') = runState (transform qstm) qs'
        liveCode = evalState (eliminateDeadCode stms) newLState
    return liveCode

testMalloc file = do 
    ast <- parseFile file
    ast' <- analyzeAST ast
    let (stm, s) = runState (translate ast') newTranslateState;
        (qstm, qs') = runState (quadStm stm) s
        (stms, s') = runState (transform qstm) qs'
        (liveCode, livestate) = runState (eliminateDeadCode stms) newLState
    return $ pt livestate


testStms file = do 
    ast <- parseFile file
    ast' <- analyzeAST ast
    let (stm, s) = runState (translate ast') newTranslateState;
        (qstm, qs') = runState (quadStm stm) s
        (stms, s') = runState (transform qstm) qs'
        -- (liveCode, livestate) = runState (eliminateDeadCode stms) newLState
    return $ zip stms [0..]

testStm = [(MOV (TEMP 2) (CONSTI 2)),(MOV (TEMP 1) (CONSTI 1)) ,(EXP (CALL (NAME "exit") [(TEMP 1)]))]