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
type Liveness = [(Int, ([Int],[Int]))]
type LGK = [(Int, ([Exp], [Exp]))]
type Live = [(Int, ([Exp], [Exp]))]
data LFlow = L {    tree :: Stm,
                    gen :: [Exp],
                    kill :: [Exp],
                    defid :: Int,
                    reTree :: [Stm]} 
                    deriving (Show, Eq)

data LState = LState {  idCount :: Int,
                        memFlow :: [Exp], 
                        wrappedFlow :: [LFlow],
                        live :: Live,
                        st :: SuccTable,
                        pt :: PredTable,
                        lock :: [Int]} deriving (Show, Eq)

newLState = LState {idCount = 0, memFlow = [], wrappedFlow = [],
                    st = [], live = [], pt = [], lock = []} 

newL :: Stm -> State LState LFlow
newL t = do 
    oldState <- get
    let count = idCount oldState
    put $ oldState {idCount = count + 1}
    return $ L {defid = count, tree = t, gen = [], kill = [], reTree = []}

wrapLGK :: [Stm] -> State LState [LFlow]
wrapLGK stms = do
    flows <- mapM addOneLGK stms
    state <- get
    put $ state {wrappedFlow = flows}
    flows' <- mapM wrapOneLGK flows
    state' <- get
    put $ state' {wrappedFlow = flows'}
    return flows'

-- wrap stm with LFlow but WITHOUT gen/kill
addOneLGK :: Stm -> State LState LFlow
addOneLGK s = newL s

-- Add Gen Kills
wrapOneLGK :: LFlow -> State LState LFlow
wrapOneLGK l@(L (MOV t (BINEXP _ a b) ) _ _ _ _) 
    = return $ l{gen = [a, b], kill = [t]}
wrapOneLGK l@(L (MOV t (MEM b _)) _ _ _ _) 
    = return $ l{gen = [b], kill = [t]}
wrapOneLGK l@(L (MOV (MEM _ _) b) _ _ _ _) = return $ l {gen = [b]}
wrapOneLGK l@(L (MOV t (CALL (NAME n) exps)) _ _ _ _) 
    | "#p_" `isPrefixOf` n || n == "memaccess" = return $ l {kill = [t]}
    | otherwise = return $ l {kill = [t], gen = exps}
wrapOneLGK l@(L (MOV t b) _ _ _ _) = return $ l {kill = [t], gen = [b]}
wrapOneLGK l@(L (CJUMP _ a b _ _ ) _ _ _ _) = return $ l {gen = [a, b]}
wrapOneLGK l@(L (EXP (CALL (NAME n) exps)) _ _ _ _) 
    | "#p_" `isPrefixOf` n || n == "memaccess" = return $ l 
    | otherwise = return $ l {gen = exps}
wrapOneLGK x = return x

genLSucc :: [LFlow] -> SuccTable
genLSucc flow = genLSucc' flow flow []

genLSucc' :: [LFlow] -> [LFlow] -> SuccTable -> SuccTable
genLSucc' src [] acc = acc
genLSucc' src ((L (CJUMP _ _ _ t f) _ _ defid _) : rest) acc 
    = genLSucc' src rest (acc ++ [(defid, (searchLable t src) ++ (searchLable f src))])
genLSucc' src ((L (JUMP (NAME l) _) _ _ defid _) : rest) acc 
    = genLSucc' src rest (acc ++ [(defid, (searchLable l src))])
genLSucc' src ((L _ _ _ defid _) : rest) acc 
    = genLSucc' src rest (acc ++ [(defid, (nextID defid src))])

genLPred :: [LFlow] -> PredTable
genLPred flow = genLPred' flow flow []

genLPred' :: [LFlow] -> [LFlow] -> PredTable -> PredTable
genLPred' src [] acc = acc
genLPred' src ((L (LABEL l) _ _ defid _) : rest) acc = genLPred' src rest (acc ++ [(defid, (searchLable l))])
    where
        searchLable :: String -> [Int]
        searchLable l = (searchLable' src l []) ++ pred
        searchLable' :: [LFlow] -> String -> [Int] -> [Int]
        searchLable' [] _ acc = acc
        searchLable' ((L (JUMP _ lables) _ _ defid _) : rest) l acc
            | elem l lables = searchLable' rest l (defid:acc)
        searchLable' ((L (CJUMP _ _ _ t f) _ _ defid _) : rest) l acc
            | l == t || l == f = searchLable' rest l (defid:acc)
        searchLable' (_:rest) l acc = searchLable' rest l acc
        pred = if (defid /= 0)&&(isNotjump (src!! (defid - 1)))
                then (prevId defid) else []
        isNotjump (L (JUMP _ _) _ _ _ _) = False
        isNotjump (L (CJUMP _ _ _ _ _) _ _ _ _) = False
        isNotjump _ = True

genLPred' src ((L _ _ _ defid _) : rest) acc = genLPred' src rest (acc ++ [(defid, (prevId defid))])

searchLable :: String -> [LFlow] -> [Int]
searchLable str ((L (LABEL lab) _ _ defid _):xs)
    | str == lab = defid : (searchLable str xs)
searchLable str (x:xs) = searchLable str xs
searchLable _ [] = []


nextID x src
    | x < (length src - 1) = [x + 1]
    | otherwise = []

initLive :: [LFlow] -> (LGK, Live)
initLive flows = (map takeLGK flows, map initL flows)
    where
        takeLGK (L tree g k defid _) = (defid, (g, k))
        initL (L _ _ _ defid _) = (defid, ([], []))

iterateLive :: LGK -> Live -> SuccTable -> Live
iterateLive gk this succ
  | this == next = this
  | otherwise = iterateLive gk next succ
  where
    next = iterateOnce this []
    iterateOnce :: Live -> Live -> Live
    iterateOnce [] acc = acc
    iterateOnce ((defid, (in_, out_)):remain) acc = iterateOnce remain (acc ++ [updated])
        where
            updated = (defid, (newIn, newOut))
            su = ((Data.List.lookup) defid succ)
            succThis = if su == Nothing then fail "Nothing!" else fromJust su
            succIn = map fromJust $ (filter (/= Nothing) (map (\x -> Data.List.lookup x this) succThis))
            newOut = if succIn == [] then [] else foldl1 union (map fst succIn)
            getgk = (Data.List.lookup) defid gk
            (gen, kill) = if getgk == Nothing then fail "Nothing!" else fromJust getgk
            newIn = union gen (newOut \\ kill)

genLive :: [LFlow] -> (Live, SuccTable, PredTable)
genLive flow = (iterateLive gk init succ, succ, pred)
    where
        (gk, init) = initLive flow
        succ = genLSucc flow
        pred = genLPred flow

eliminateDeadCode :: [Stm] -> State LState [Stm]
eliminateDeadCode stms = do
    state <- get
    let (gk, gkstate) = runState (wrapLGK stms) state
    put gkstate
    mapM (addreTree) (wrappedFlow gkstate)
    recursiveElim
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
    let stms = unL $ wrappedFlow state
        (gk, gkstate) = runState (wrapLGK stms) newLState
        (live_, st_, pt_) = genLive gk
    put $ gkstate {st = st_, live = live_, pt = pt_} -- put everything in the state
    gkstate' <- get
    mapM (lockUsed) (wrappedFlow gkstate')
    mapM (addreTree) (wrappedFlow gkstate')
    elimAll
    clearNoTemp
    removeEmpty
    state' <- get
    let oldflow = wrappedFlow state
        newflow = wrappedFlow state'
    if oldflow == newflow then
        return ()
    else
        recursiveElim

removeEmpty :: State LState ()
removeEmpty = do
    state <- get
    let oldFlow = wrappedFlow state
    put $ state { wrappedFlow = filter (\x -> reTree x /= []) oldFlow}
    return () 
    
elimAll :: State LState ()
elimAll = do
    state <- get
    mapM elimOne [0..(length (wrappedFlow state) - 1)]
    return ()

elimOne :: Int -> State LState ()
elimOne targetNum = do
    state <- get
    let flows = (wrappedFlow state)
        targetFlow = flows !! targetNum
        liveTable = live state
        thisLive = Data.List.lookup targetNum liveTable
        locks = lock state
        (liveIn, liveOut) = if thisLive == Nothing then fail (show liveTable) else fromJust thisLive
    if (not $ sideEffect targetFlow (unL flows)) && (not $ elem targetNum locks) then
        case (tree targetFlow) of 
            (MOV (TEMP t) _) -> if (notSpecial t) && (not $ elem (TEMP t) liveOut) then do
                                    updateLFlow $ targetFlow {reTree = []}
                                else return ()
            otherwise -> return ()
    else
        return ()

notSpecial t = not $ elem t [0, 1, 2, 13, 14, 15]

lockUsed :: LFlow -> State LState ()
lockUsed l@(L (MOV _ c@(CALL _ exps )) _ _ defid _) = getLocks exps l

lockUsed l@(L (EXP c@(CALL _ exps )) _ _ defid _) = getLocks exps l

lockUsed l@(L (MOV t m@(MEM _ _ )) _ _ defid _) = getLocks [m] l

lockUsed _ = return ()

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
findDec dec cur pt flows 
    | found = [cur]
    | otherwise = concatMap (\x -> findDec dec x pt flows) next
    where
        found = startswith (tree (flows !! cur)) dec
        next = fromJust $ Data.List.lookup cur pt

startswith :: Stm -> Exp -> Bool
startswith (MOV (MEM (CALL (NAME "#memaccess") [CONSTI i11, CONSTI i12]) _) _) 
            (MEM (CALL (NAME "#memaccess") [CONSTI i21, CONSTI i22]) _) 
    = (i11 -i12) == (i21 - i22)
startswith (MOV a _) target = a == target
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

clearNoTemp :: State LState ()
clearNoTemp =  do
    state <- get
    -- fail $ show (lock state)
    mapM (clearOne (lock state)) (wrappedFlow state)
    return ()

clearOne :: [Int] -> LFlow -> State LState ()
clearOne locks flow
    | (noTemp flow) &&  (not $ elem (defid flow) locks) = updateLFlow $ flow {reTree = []}
    | otherwise = return ()

clearUsage :: Int -> State LState ()
clearUsage temp = do
    state <- get
    mapM (rmIfContains temp) (wrappedFlow state)
    return ()

rmIfContains :: Int -> LFlow -> State LState ()
rmIfContains temp flow
    | (contains (TEMP temp) flow) = updateLFlow $ flow {reTree = []}
    | otherwise = return ()


contains :: Exp -> LFlow -> Bool
--s1
contains target (L (MOV a expr@(BINEXP _ b c )) _ _ _ _)
    | b == target || c == target = True
--s5
contains target (L (MOV a expr@(MEM b _)) _ _ _ _)
    | b == target = True
--s9
contains target (L (MOV a expr@(CALL e es)) _ _ _ _)
    | elem target (e:es) = True
--s8
contains target (L (EXP expr@(CALL e es)) _ _ _ _)
    | elem target (e:es) = True
--s6
contains target (L (MOV expr@(MEM a _) b) _ _ _ _)
    | a == target = True

--s3
contains _ _ = False

noTemp :: LFlow -> Bool
--s1
noTemp (L (MOV a expr) _ _ _ _)
    | exprNoTemp a && exprNoTemp expr = True
--s3
noTemp _ = False

exprNoTemp (TEMP _) = False
exprNoTemp (BINEXP _ a b) = (exprNoTemp a) && (exprNoTemp b)
exprNoTemp (MEM e _) = exprNoTemp e 
exprNoTemp (CALL _ exprs) = and (map exprNoTemp exprs)
exprNoTemp _ = True

sideEffect :: LFlow -> [Stm] -> Bool
-- sideEffect l@(L (MOV t (MEM _ _)) _ _ _ _) = True
-- sideEffect l@(L (MOV (MEM _ _) b) _ _ _ _) = True
sideEffect l@(L (MOV t (CALL (NAME n) exps)) _ _ _ _) _
    | "#p_" `isPrefixOf` n || n == "exit" = True
sideEffect l@(L (CJUMP _ a b _ _ ) _ _ _ _) _ = True
sideEffect l@(L (EXP (CALL (NAME n) exps)) _ _ _ _) _
    | "#p_" `isPrefixOf` n || n == "exit" = True
-- sideEffect l@(L (MOV t (BINEXP rop a b)) _ _ _ _) ref
--     | elem rop [PLUS, MINUS, MUL, DIV, MOD] = True
sideEffect x _= False

testDeadCode file = do 
    ast <- parseFile file
    ast' <- analyzeAST ast
    let (stm, s) = runState (translate ast') newTranslateState;
        (qstm, qs') = runState (quadStm stm) s
        (stms, s') = runState (transform qstm) qs'
        liveCode = evalState (eliminateDeadCode stms) newLState
    return liveCode

seeLive file = do
    ast <- parseFile file
    ast' <- analyzeAST ast
    let (stm, s) = runState (translate ast') newTranslateState;
        (qstm, qs') = runState (quadStm stm) s
        (stms, s') = runState (transform qstm) qs'
        (gk, gkstate) = runState (wrapLGK stms) newLState
        (live_, st_, _) = genLive gk
    return gk 

seeLiveStm stms = live_
    where
        (gk, gkstate) = runState (wrapLGK stms) newLState
        (live_, st_, _) = genLive gk


testStm = [(MOV (TEMP 2) (CONSTI 2)),(MOV (TEMP 1) (CONSTI 1)) ,(EXP (CALL (NAME "exit") [(TEMP 1)]))]