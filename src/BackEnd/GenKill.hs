module BackEnd.GenKill where
import Control.Monad.State.Lazy
import BackEnd.IR 
import Data.HashMap as HashMap hiding (map)
import BackEnd.Translate

type PredTable = [(Int, [Int])]
type ReachingGK = [(Int, ([Int], [Int]))]
type ReachingDef = [(Int, ([Int], [Int]))]
type AGK = [(Int, ([Exp], [Exp]))]
type ADef = [(Int, ([Exp], [Exp]))]
type ReachingExpr = [(Int, [Exp])]

data ReachFlow = M { tree :: Stm,
                    gen :: [Int],
                    kill :: [Int],
                    defid :: Int}
                | E {tree :: Stm,
                     defid :: Int} deriving (Show, Eq)

data ReachState = ReachState { idCount :: Int,
                               tempMap :: HashMap.Map Int [Int]}

newReachState = ReachState {idCount = 0, tempMap = HashMap.empty}

reachMov :: Stm -> State ReachState (Int, ReachFlow)
reachMov t = do 
    oldState <- get
    let count = idCount oldState
    put $ oldState {idCount = count + 1}
    return (count, M {defid = count, tree = t, gen = [count], kill = []})

reachExp :: Stm -> State ReachState ReachFlow
reachExp e = do
    oldState <- get
    let count = idCount oldState
    put $ oldState {idCount = count + 1}
    return $ E {tree = e, defid = count}

data AFlow = A {    tree_ :: Stm,
                    gen_ :: [Exp],
                    kill_ :: [Exp],
                    defid_ :: Int,
                    reTree_ :: [Stm]} 
                    deriving (Show, Eq)

data AState = AState {  idCount_ :: Int,
                        memFlow :: [Exp], 
                        wrappedFlow :: [AFlow],
                        allExpr :: [Exp],
                        re :: ReachingExpr,
                        trans :: TranslateState,
                        pt :: PredTable}

newAState = AState {idCount_ = 0, memFlow = [], wrappedFlow = [], allExpr = [], re = [],
                    trans = newTranslateState, pt = []} -- trans is for cse and is usd temporarily

newA :: Stm -> State AState AFlow
newA t = do 
    oldState <- get
    let count = idCount_ oldState
    put $ oldState {idCount_ = count + 1}
    return $ A {defid_ = count, tree_ = t, gen_ = [], kill_ = [], reTree_ = []}
