module BackEnd.GenKill where
import Control.Monad.State.Lazy
import BackEnd.IR 
import Data.HashMap as HashMap hiding (map)


data DataFlow = M { tree :: Stm,
                    gen :: [Int],
                    kill :: [Int],
                    defid :: Int}
                | E {tree :: Stm,
                     defid :: Int} deriving (Show, Eq)

data DataState = DataState { idCount :: Int,
                             dataset :: [DataFlow],
                             tempMap :: HashMap.Map Int [Int]}

newDataState = DataState {idCount = 0, dataset = [], tempMap = HashMap.empty}

newMov :: Stm -> State DataState (Int, DataFlow)
newMov t = do 
    oldState <- get
    let count = idCount oldState
    put $ oldState {idCount = count + 1}
    return (count, M {defid = count, tree = t, gen = [count], kill = []})

newExp :: Stm -> State DataState DataFlow
newExp e = do
    oldState <- get
    let count = idCount oldState
    put $ oldState {idCount = count + 1}
    return $ E {tree = e, defid = count}