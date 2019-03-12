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
import BackEnd.DataFlow hiding (addreTree)
    
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
                        st :: SuccTable} deriving (Show, Eq)

newLState = LState {idCount = 0, memFlow = [], wrappedFlow = [], st = [], live = []} 

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
    | "#p_" `isPrefixOf` n = return $ l {kill = [t]}
    | otherwise = return $ l {kill = [t], gen = exps}
wrapOneLGK l@(L (MOV t b) _ _ _ _) = return $ l {kill = [t], gen = [b]}
wrapOneLGK l@(L (CJUMP _ a b _ _ ) _ _ _ _) = return $ l {gen = [a, b]}
wrapOneLGK l@(L (EXP (CALL (NAME n) exps)) _ _ _ _) 
    | "#p_" `isPrefixOf` n = return $ l 
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

genLive :: [LFlow] -> (Live, SuccTable)
genLive flow = (iterateLive gk init succ, succ)
    where
        (gk, init) = initLive flow
        succ = genLSucc flow

eliminateDeadCode :: [Stm] -> State LState [Stm]
eliminateDeadCode stms = do
    state <- get
    let (gk, gkstate) = runState (wrapLGK stms) state
    put gkstate
    mapM (addreTree) (wrappedFlow gkstate)
    recursiveElim
    state' <- get
    return $ unL $ wrappedFlow state'

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
        (live_, st_) = genLive gk
    put $ gkstate {st = st_, live = live_} -- put everything in the state
    gkstate' <- get
    mapM (addreTree) (wrappedFlow gkstate')
    elimAll
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
    let targetFlow = (wrappedFlow state) !! targetNum
        liveTable = live state
        thisLive = Data.List.lookup targetNum liveTable
        (liveIn, liveOut) = if thisLive == Nothing then fail (show liveTable) else fromJust thisLive
    if (not $ sideEffect targetFlow) then
        case (tree targetFlow) of 
            (MOV (TEMP t) expr) -> if not $ elem (TEMP t) liveOut then
                                    --clearMem t >>
                                    updateLFlow $ targetFlow {reTree = []}
                                else return ()
            otherwise -> return ()
    else
        return ()

clearMem :: Int -> State LState ()
clearMem temp = undefiend

sideEffect :: LFlow -> Bool
-- sideEffect l@(L (MOV t (MEM _ _)) _ _ _ _) = True
-- sideEffect l@(L (MOV (MEM _ _) b) _ _ _ _) = True
sideEffect l@(L (MOV t (CALL (NAME n) exps)) _ _ _ _) 
    | "#p_" `isPrefixOf` n || n == "exit" = True
sideEffect l@(L (CJUMP _ a b _ _ ) _ _ _ _) = True
sideEffect l@(L (EXP (CALL (NAME n) exps)) _ _ _ _) 
    | "#p_" `isPrefixOf` n || n == "exit" = True
sideEffect l@(L (MOV t (BINEXP rop _ _)) _ _ _ _)
    | elem rop [PLUS, MINUS, MUL, DIV, MOD] = True
sideEffect x = False

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
        (live_, st_) = genLive gk
    return live_ 

seeLiveStm stms = live_
    where
        (gk, gkstate) = runState (wrapLGK stms) newLState
        (live_, st_) = genLive gk



testStm = [(MOV (TEMP 2) (CONSTI 2)),(MOV (TEMP 1) (CONSTI 1)) ,(EXP (CALL (NAME "exit") [(TEMP 1)]))]