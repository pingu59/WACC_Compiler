module BackEnd.GenKill where
import Control.Monad.State.Lazy
import BackEnd.IR 
import Data.HashMap as HashMap hiding (map)

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

data AFlow = A { tree_ :: Stm,
                    gen_ :: [Exp],
                    kill_ :: [Exp],
                    defid_ :: Int} deriving (Show, Eq)

data AState = AState { idCount_ :: Int,
                        memFlow :: [Exp], 
                        dummyFlow :: [AFlow],
                        allExpr :: [Exp]}

newAState = AState {idCount_ = 0, memFlow = [], dummyFlow = [], allExpr = []}

newA :: Stm -> State AState AFlow
newA t = do 
    oldState <- get
    let count = idCount_ oldState
    put $ oldState {idCount_ = count + 1}
    return $ A {defid_ = count, tree_ = t, gen_ = [], kill_ = []}
