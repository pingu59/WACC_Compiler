module BackEnd.ReachFlow where
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
3. take the canonical quadruples and perform analysis --done
4. transform
-}

type PredTable = [(Int, [Int])]
type ReachingGK = [(Int, ([Int], [Int]))]
type ReachingDef = [(Int, ([Int], [Int]))]
type AGK = [(Int, ([Exp], [Exp]))]
type ADef = [(Int, ([Exp], [Exp]))]
type ReachingExpr = [(Int, [Exp])]

isBM :: Exp -> Bool
isBM (MEM _ _) = True
isBM (BINEXP _ _ _) = True
isBM _ = False

testReachGKFile file = do
    ast <- parseFile file
    ast' <- analyzeAST ast
    let (stm, s) = runState (translate ast') newTranslateState;
        userFrags = map (\(PROC stm _) -> stm) (procFrags s)
        (qstm, qs') = runState (quadStm stm) s
        (qfrag, qs'') = runState (mapM quadStm userFrags) qs'
        (stms, s') = runState (transform qstm) qs''
        (userFrags', _) = runState (mapM transform qfrag) s'
        (gkmain, gkstate) = runState (wrapReachGK stms) newReachState
        (gkuser) = evalState (mapM wrapReachGK userFrags') gkstate
    return $ genReachingDef (gkmain ++ concat gkuser)

testAGKFile file = do
    ast <- parseFile file
    ast' <- analyzeAST ast
    let (stm, s) = runState (translate ast') newTranslateState;
        userFrags = map (\(PROC stm _) -> stm) (procFrags s)
        (qstm, qs') = runState (quadStm stm) s
        (qfrag, qs'') = runState (mapM quadStm userFrags) qs'
        (stms, s') = runState (transform qstm) qs''
        (userFrags', _) = runState (mapM transform qfrag) s'
        (gkmain, gkstate) = runState (wrapAGK stms) newAState
        (gkuser) = evalState (mapM wrapAGK userFrags') gkstate
    return $ genADef (gkmain ++ concat gkuser)

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

{-new-}
quadStm (MOV e1 e2) = do
  e1' <- quadExp e1
  e2' <- quadExp e2
  if(isBM e1' && isBM e2') then do
    eseq' <- eseq
    return $ MOV e1' (eseq' e2')
  else
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

--- Reaching Definition --- 

getTempDefts :: Int -> State ReachState [Int]
getTempDefts k = do
    state <- get
    let map = tempMap state
        deftsT = HashMap.lookup k map
    case deftsT of
        Just a -> return a
        Nothing -> return []

-- wrap gk data structure for both types of analysis
wrapReachGK :: [Stm] -> State ReachState [ReachFlow]
wrapReachGK stms = do
    stms' <- (mapM addOneReachDef stms)
    flows <- mapM wrapOneReachGk stms'
    return flows

movReachGK m a = do
    (count, mov) <- reachMov m
    state <- get
    old <- getTempDefts a
    put $ state {tempMap = HashMap.insert a (count:old) (tempMap state)}
    return $ mov

getReachKill m a gen = do
    deftsT <- getTempDefts a
    return $ m {kill = deftsT\\gen}

addOneReachDef :: Stm -> State ReachState ReachFlow
addOneReachDef m@(MOV (TEMP a) b) = movReachGK m a
addOneReachDef e = reachExp e

wrapOneReachGk :: ReachFlow -> State ReachState ReachFlow 
wrapOneReachGk m@(M (MOV (TEMP a) _) gen _ _) = getReachKill m a gen
wrapOneReachGk x = return x

genReachPred :: [ReachFlow] -> PredTable
genReachPred flow = genReachPred' flow flow [] 

genReachPred' :: [ReachFlow] -> [ReachFlow] -> PredTable -> PredTable
genReachPred' src [] acc = acc
genReachPred' src ((E (LABEL l) deftid) : rest) acc = genReachPred' src rest (acc ++ [(deftid, (searchLable l))])
    where
        searchLable :: String -> [Int]
        searchLable l = (searchLable' src l []) ++ pred
        searchLable' :: [ReachFlow] -> String -> [Int] -> [Int]
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

genReachPred' src ((M _ _ _ deftid) : rest) acc = genReachPred' src rest (acc ++ [(deftid, (prevId deftid))])
genReachPred' src ((E _ deftid) : rest) acc = genReachPred' src rest (acc ++ [(deftid, (prevId deftid))])

prevId 0 = []
prevId x = [x - 1]

--              deftid  in          gkout                       init ReachingDef                   
initReachingDef :: [ReachFlow] -> (ReachingGK , ReachingDef)
initReachingDef flows = (map takeReachGK flows, map initReach flows) 
    where
        takeReachGK (M tree g k deftid) = (deftid, (g, k))
        takeReachGK (E tree deftid) = (deftid, ([], []))
        initReach (M _ _ _ deftid) = (deftid, ([], []))
        initReach (E tree deftid) = (deftid, ([], []))

--                    gk table                     current reaching def         pred table                 output reaching def
iterateReachingDef :: ReachingGK -> ReachingDef -> PredTable -> ReachingDef
iterateReachingDef gk this pred
  | this == next = this
  | otherwise = iterateReachingDef gk next pred
  where
    next = iterateOnce this []
    iterateOnce :: ReachingDef -> ReachingDef ->  ReachingDef
    iterateOnce [] acc = acc
    iterateOnce ((deftid, (in_, out_)):remain) acc = iterateOnce remain (acc ++ [updated])
        where
            updated = (deftid, (newIn, newOut))
            predThis = fromJust ((Data.List.lookup) deftid pred)
            predOut = map fromJust $ (filter (/= Nothing) (map (\x -> Data.List.lookup x this) predThis))
            newIn = if predOut == [] then [] else foldl1 union (map snd predOut)
            (gen, kill) = fromJust $ (Data.List.lookup) deftid gk
            newOut = union  gen (in_ \\ kill)

genReachingDef :: [ReachFlow] -> ReachingDef
genReachingDef flow = iterateReachingDef gk init pred
    where
        (gk, init) = initReachingDef flow
        pred = genReachPred flow

reachingDefSample = [MOV (TEMP 1) (CONSTI 5), MOV (TEMP 2) (CONSTI 1), LABEL "L1",
                     CJUMP BackEnd.IR.LT (TEMP 2) (TEMP 1) "L2" "LNEXT", LABEL "LNEXT",
                     MOV (TEMP 2) (BINEXP PLUS (TEMP 2) (TEMP 2)), JUMP (NAME "L1") ["L1"],
                     LABEL "L2", MOV (TEMP 1) (BINEXP MINUS (TEMP 2) (TEMP 1)), MOV (TEMP 2) (CONSTI 0)]

testReachingDef stms = do
    let flow = evalState (wrapReachGK stms) newReachState
        ret = genReachingDef flow 
    return $ ret

testPred stms = do
    let flow = evalState (wrapReachGK stms) newReachState
        ret = genReachPred flow 
    return $ ret

testReachGK stms = do
    let flow = evalState (wrapReachGK stms) newReachState
    return $ flow

--- Available Expression --- 

--                                          t       mem
containsExpression :: Exp -> State AState [Exp]
containsExpression target = do
    state <- get
    return $ nub $ concatMap (contains target) (dummyFlow state)

containsMem :: [AFlow] -> [Exp]
containsMem flows = concatMap containsOneMem flows

containsOneMem :: AFlow -> [Exp]
containsOneMem (A (MOV a e@(MEM b _)) _ _ deftid) = [e]
containsOneMem (A (MOV e@(MEM a _) b) _ _ deftid) = [e]
containsOneMem _ = []

contains :: Exp -> AFlow -> [Exp]
--s1
contains target (A (MOV a expr@(BINEXP _ b c )) _ _ deftid) 
    | b == target || c == target = [expr]
--s5
contains target (A (MOV a expr@(MEM b _)) _ _ deftid)
    | b == target = [expr]
--s9
contains target (A (MOV a expr@(CALL e es)) _ _ deftid)
    | elem target (e:es) = [expr]
--s8
contains target (A (EXP expr@(CALL e es)) _ _ deftid)
    | elem target (e:es) = [expr]
--s6
contains target (A (MOV expr@(MEM a _) b) _ _ deftid)
    | a == target = [expr]

--s3
contains _ _ = []

wrapAGK :: [Stm] -> State AState [AFlow]
wrapAGK stms = do
    flows <- mapM addOneAGK stms
    state <- get 
    put $ state {memFlow = containsMem flows, dummyFlow = flows}
    flows' <- mapM wrapOneAGK flows
    return flows'

-- wrap stm with AFlow but WITHOUT gen/kill
addOneAGK :: Stm -> State AState AFlow 
addOneAGK s = newA s

killMem :: AFlow -> State AState AFlow
killMem e = do
    state <- get
    return $ e {kill_ = memFlow state} 

addExpr :: [Exp] -> State AState ()
addExpr exprs = do
    state <- get 
    put $ state {allExpr = union (allExpr state) exprs}

-- Add Gen Kills
wrapOneAGK :: AFlow -> State AState AFlow
wrapOneAGK a@(A (EXP e@(CALL _ _)) _ _ _) = addExpr [e] >> killMem a

wrapOneAGK a@(A (MOV (MEM _ _) _ ) _ _ _) = killMem a
--Pre : t is a temp
wrapOneAGK a@(A (MOV t (CALL _ _)) _ _ _) = do
    state <- get
    cexpr <- containsExpression t
    return $ a {kill_ = union (memFlow state) cexpr} 

wrapOneAGK a@(A (MOV t b) _ _ _) = do
    cexpr <- containsExpression t 
    return $ a {kill_ = cexpr, gen_ = ([b]\\cexpr)}

wrapOneAGK x = return x

genAPred :: [AFlow] -> PredTable
genAPred flow = genAPred' flow flow [] 

genAPred' :: [AFlow] -> [AFlow] -> PredTable -> PredTable
genAPred' src [] acc = acc
genAPred' src ((A (LABEL l) _ _ deftid) : rest) acc = genAPred' src rest (acc ++ [(deftid, (searchLable l))])
    where
        searchLable :: String -> [Int]
        searchLable l = (searchLable' src l []) ++ pred
        searchLable' :: [AFlow] -> String -> [Int] -> [Int]
        searchLable' [] _ acc = acc
        searchLable' ((A (JUMP _ lables) _ _ deftid) : rest) l acc
            | elem l lables = searchLable' rest l (deftid:acc)
        searchLable' ((A (CJUMP _ _ _ t f) _ _ deftid) : rest) l acc 
            | l == t || l == f = searchLable' rest l (deftid:acc)
        searchLable' (_:rest) l acc = searchLable' rest l acc
        pred = if (deftid /= 0)&&(isNotjump (src!! (deftid - 1))) 
               then (prevId deftid) else []
        isNotjump (A (JUMP _ _) _ _ _) = False
        isNotjump (A (CJUMP _ _ _ _ _) _ _ _) = False
        isNotjump _ = True

genAPred' src ((A _ _ _ deftid) : rest) acc = genAPred' src rest (acc ++ [(deftid, (prevId deftid))])

--              deftid  in          gkout                       init adef                   
initADef :: [AFlow] -> ( AGK, ADef)
initADef flows = (map takeAGK flows, map initA flows) 
    where
        takeAGK (A tree g k deftid) = (deftid, (g, k))
        initA (A _ _ _ deftid) = (deftid, ([], []))

iterateADef :: AGK -> ADef -> PredTable -> ADef
iterateADef gk this pred
  | this == next = this 
  | otherwise = iterateADef gk next pred
  where
    next = iterateOnce this []
    iterateOnce :: ADef -> ADef -> ADef
    iterateOnce [] acc = acc
    iterateOnce ((deftid, (in_, out_)):remain) acc = iterateOnce remain (acc ++ [updated])
        where 
            updated = (deftid, (newIn, newOut))
            predThis = fromJust ((Data.List.lookup) deftid pred)
            predOut = map fromJust $ (filter (/= Nothing) (map (\x -> Data.List.lookup x this) predThis)) 
            newIn = if predOut == [] then [] else foldl1 intersect (map snd predOut)
            (gen, kill) = fromJust $ (Data.List.lookup) deftid gk
            newOut = union gen (in_ \\ kill)

genADef :: [AFlow] -> ADef
genADef flow = iterateADef gk init pred
    where
        (gk, init) = initADef flow
        pred = genAPred flow

genReachingExpression :: ADef -> ReachingExpr
genReachingExpression adef = map reachingOneExpression adef

reachingOneExpression :: (Int, ([Exp], [Exp])) -> (Int, [Exp])
reachingOneExpression (deftid, (in_, out_)) 
    = (deftid, subset)
    where
        subset = nub $ concatMap (genOneReachable) (intersect in_ out_)
        genOneReachable :: Exp -> [Exp]
        genOneReachable a@(BINEXP _ b c) = [a, b, c]
        genOneReachable a@(MEM b _) = [b]
        genOneReachable _ = fail "EXPRESSION CONTAINS NOT ALLOWED GENS"
