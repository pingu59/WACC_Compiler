module BackEnd.DataFlow where
import BackEnd.Canon
import BackEnd.Translate
import BackEnd.IR 
import Control.Monad.State.Lazy
import BackEnd.Frame
import FrontEnd.Parser
import FrontEnd.SemanticAnalyzer
import BackEnd.GenKill
import Data.HashMap as HashMap hiding (map, (\\), union, filter)
import Data.Maybe
import Data.List

{-
1. take translation from translate and change them to quadruples -- done!
2. feed the quadruples into canon -- done ?
3. take the canonical quadruples and perform analysis
4. transform
-}

isBM :: Exp -> Bool
isBM (MEM _ _) = True
isBM (BINEXP _ _ _) = True
isBM _ = False

testGKFile file = do
    ast <- parseFile file
    ast' <- analyzeAST ast
    let (stm, s) = runState (translate ast') newTranslateState;
        userFrags = map (\(PROC stm _) -> stm) (procFrags s)
        (qstm, qs') = runState (quadStm stm) s
        (qfrag, qs'') = runState (mapM quadStm userFrags) qs'
        (stms, s') = runState (transform qstm) qs''
        (userFrags', _) = runState (mapM transform qfrag) s'
        (gkmain, gkstate) = runState (wrapGK stms) newDataState
        (gkuser) = evalState (mapM wrapGK userFrags') gkstate
    return $ genReachingDef (gkmain ++ concat gkuser)

eseq :: State TranslateState (Exp -> Exp)
eseq = do 
    t <- newTemp
    return $ \e -> (ESEQ (MOV (TEMP t) e) (TEMP t))

twoExpr :: Exp -> Exp -> (Exp -> Exp -> a) -> State TranslateState a 
twoExpr e1 e2 a = do
    e1' <- quadExp e1
    e2' <- quadExp e2
    if (isBM e1') then do
        eseq1 <- eseq
        if (isBM e2') then do
            eseq2 <- eseq
            return $ a (eseq1 e1') (eseq2 e2')
        else
            return $ a (eseq1 e1') e2'
    else do
        if (isBM e2') then do
            eseq2 <- eseq
            return $ a e1' (eseq2 e2')
        else
            return $ a e1' e2'

quadStm :: Stm -> State TranslateState Stm
quadStm (EXP e) = do 
    e' <- quadExp e
    return $ EXP e' 

quadStm (SEQ s1 s2) = do 
    s1' <- quadStm s1
    s2' <- quadStm s2
    return $ SEQ s1' s2'

quadStm (MOV e1 e2) = do
    e1' <- quadExp e1
    e2' <- quadExp e2
    return $ MOV e1' e2'

quadStm (JUMP e ls) = do 
    e' <- quadExp e
    if (isBM e) then do
        eseq' <- eseq
        return $ JUMP (eseq' e') ls
    else
        return $ JUMP e' ls

quadStm (CJUMP rop e1 e2 t f) = do
    twoExpr e1 e2 (\a -> \b -> (CJUMP rop a b t f))

quadStm x = return x

quadExp :: Exp -> State TranslateState Exp
quadExp (BINEXP bop e1 e2) = do
    twoExpr e1 e2 (\a -> \b -> (BINEXP bop a b))

quadExp (MEM e i) = do
    e' <- quadExp e
    if(isBM e) then do
        eseq' <- eseq
        return (MEM (eseq' e') i)
    else
        return (MEM e' i)

quadExp (CALL name es) = do
    es' <- mapM (\e -> quadExp e) es
    return (CALL name es')

quadExp (ESEQ s e) = do
    s' <- quadStm s
    e' <- quadExp e
    return (ESEQ s' e')
    
quadExp x = return x

--- Wrapping trees to gen/kill format --- 
getdefts :: Int -> State DataState [Int]
getdefts k = do
    state <- get
    let map = tempMap state
        deftsT = HashMap.lookup k map
    case deftsT of
        Just a -> return a 
        Nothing -> return []


wrapGK :: [Stm] -> State DataState [DataFlow]
wrapGK stms = do
    stms' <- (mapM addOneDef stms)
    flows <- mapM wrapOneGk stms'
    return flows

movGK m a = do
    (count, mov) <- newMov m
    state <- get
    old <- getdefts a
    put $ state {tempMap = HashMap.insert a (count:old) (tempMap state)}
    return $ mov

getKill m a gen = do
    deftsT <- getdefts a
    return $ m {kill = deftsT\\gen}

addOneDef :: Stm -> State DataState DataFlow
addOneDef m@(MOV (TEMP a) _) = movGK m a

addOneDef e = newExp e

wrapOneGk :: DataFlow -> State DataState DataFlow 
wrapOneGk m@(M (MOV (TEMP a) _) gen _ _) = getKill m a gen

wrapOneGk x = return x

genPred :: [DataFlow] -> [(Int, [Int])]
genPred flow = genPred' flow flow [] 

genPred' :: [DataFlow] -> [DataFlow] -> [(Int, [Int])] -> [(Int, [Int])]
genPred' src [] acc = acc
genPred' src ((E (LABEL l) deftid) : rest) acc = genPred' src rest (acc ++ [(deftid, (searchLable l))])
    where
        searchLable :: String -> [Int]
        searchLable l = (searchLable' src l []) ++ pred
        searchLable' :: [DataFlow] -> String -> [Int] -> [Int]
        searchLable' [] _ acc = acc
        searchLable' ((E (JUMP _ lables) deftid) : rest) l acc
            | elem l lables = searchLable' rest l (deftid:acc)
        searchLable' ((E (CJUMP _ _ _ t f) deftid) : rest) l acc 
            | l == t || l == f = searchLable' rest l (deftid:acc)
        searchLable' (_:rest) l acc = searchLable' rest l acc
        pred = if (deftid /= 0)&&(isNotjump (src!! (deftid - 1))) 
               then (prevId deftid) else []
        isNotjump (E (JUMP _ _) _) = False
        isNotjump (E (CJUMP _ _ _ _ _) _) = False
        isNotjump _ = True

genPred' src ((M _ _ _ deftid) : rest) acc = genPred' src rest (acc ++ [(deftid, (prevId deftid))])
genPred' src ((E _ deftid) : rest) acc = genPred' src rest (acc ++ [(deftid, (prevId deftid))])

prevId 0 = []
prevId x = [x - 1]

--              deftid  in          gkout                       init reachingdef                   
initReachingDef :: [DataFlow] -> ([(Int, ([Int], [Int]))], ([(Int, ([Int], [Int]))]))
initReachingDef flows = (map takeGK flows, map initReach flows) 
    where
        takeGK (M tree g k deftid) = (deftid, (g, k))
        takeGK (E tree deftid) = (deftid, ([], []))
        initReach (M _ _ _ deftid) = (deftid, ([], []))
        initReach (E tree deftid) = (deftid, ([], []))

--                    gk table                     current reaching def         pred table                 output reaching def
iterateReachingDef :: [(Int, ([Int], [Int]))] -> [(Int, ([Int], [Int]))] -> [(Int, [Int])] -> [(Int, ([Int], [Int]))]
iterateReachingDef gk this pred
  | this == next = this 
  | otherwise = iterateReachingDef gk next pred
  where
    next = iterateOnce this []
    iterateOnce :: [(Int, ([Int], [Int]))] -> [(Int, ([Int], [Int]))] ->  [(Int, ([Int], [Int]))]
    iterateOnce [] acc = acc
    iterateOnce ((deftid, (in_, out_)):remain) acc = iterateOnce remain (acc ++ [updated])
        where 
            updated = (deftid, (newIn, newOut))
            predThis = fromJust ((Data.List.lookup) deftid pred)
            predOut = map fromJust $ (filter (/= Nothing) (map (\x -> Data.List.lookup x this) predThis)) 
            newIn = if predOut == [] then [] else foldl1 union (map snd predOut)
            (gen, kill) = fromJust $ (Data.List.lookup) deftid gk
            newOut = union  gen (in_ \\ kill)

genReachingDef :: [DataFlow] -> [(Int, ([Int], [Int]))]
genReachingDef flow = iterateReachingDef gk init pred
    where
        (gk, init) = initReachingDef flow
        pred = genPred flow


reachingDefSample = [MOV (TEMP 1) (CONSTI 5), MOV (TEMP 2) (CONSTI 1), LABEL "L1", 
                     CJUMP BackEnd.IR.LT (TEMP 2) (TEMP 1) "L2" "LNEXT", LABEL "LNEXT",
                     MOV (TEMP 2) (BINEXP PLUS (TEMP 2) (TEMP 2)), JUMP (NAME "L1") ["L1"], 
                     LABEL "L2", MOV (TEMP 1) (BINEXP MINUS (TEMP 2) (TEMP 1)), MOV (TEMP 2) (CONSTI 0)]

testReachingDef stms = do
    let flow = evalState (wrapGK stms) newDataState
        ret = genReachingDef flow 
    return $ ret

testPred stms = do
    let flow = evalState (wrapGK stms) newDataState
        ret = genPred flow 
    return $ ret

testGK stms = do
    let flow = evalState (wrapGK stms) newDataState
    return $ flow