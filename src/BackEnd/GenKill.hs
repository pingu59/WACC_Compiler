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
                    defid :: Int,
                    reTree :: [Stm]}
                | E {tree :: Stm,
                     defid :: Int,
                     reTree :: [Stm]} deriving (Show, Eq)

data ReachState = ReachState { idCount :: Int,
                               tempMap :: HashMap.Map Int [Int],
                               pt :: PredTable,
                               wrappedFlow :: [ReachFlow],
                               rd :: ReachingDef}

newReachState = ReachState {idCount = 0, tempMap = HashMap.empty, pt = [], wrappedFlow = [],
                            rd = []}

reachMov :: Stm -> State ReachState (Int, ReachFlow)
reachMov t = do 
    oldState <- get
    let count = idCount oldState
    put $ oldState {idCount = count + 1}
    return (count, M {defid = count, tree = t, gen = [count], kill = [], reTree = []})

reachExp :: Stm -> State ReachState ReachFlow
reachExp e = do
    oldState <- get
    let count = idCount oldState
    put $ oldState {idCount = count + 1}
    return $ E {tree = e, defid = count, reTree = []}

data AFlow = A {    tree_ :: Stm,
                    gen_ :: [Exp],
                    kill_ :: [Exp],
                    defid_ :: Int,
                    reTree_ :: [Stm]} 
                    deriving (Show, Eq)

data AState = AState {  idCount_ :: Int,
                        memFlow_ :: [Exp], 
                        wrappedFlow_ :: [AFlow],
                        allExpr_ :: [Exp],
                        re_ :: ReachingExpr,
                        trans_ :: TranslateState,
                        pt_ :: PredTable}

newAState = AState {idCount_ = 0, memFlow_ = [], wrappedFlow_ = [], allExpr_ = [], re_ = [],
                    trans_ = newTranslateState, pt_ = []} -- trans is for cse and is usd temporarily

newA :: Stm -> State AState AFlow
newA t = do 
    oldState <- get
    let count = idCount_ oldState
    put $ oldState {idCount_ = count + 1}
    return $ A {defid_ = count, tree_ = t, gen_ = [], kill_ = [], reTree_ = []}
