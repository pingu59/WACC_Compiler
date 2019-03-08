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

type ReachingDef = [(Int, ([Int], [Int]))]
type PredTable = [(Int, [Int])]

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
        (gkmain, gkstate) = runState (wrapGK stms) newDataState --[DataFlow]
        (gkuser) = evalState (mapM wrapGK userFrags') gkstate
    return $ genReachingDef (gkmain ++ concat gkuser)

testQuadFile file = do
    ast <- parseFile file
    ast' <- analyzeAST ast
    let (stm, s) = runState (translate ast') newTranslateState;
        userFrags = map (\(PROC stm _) -> stm) (procFrags s)
        (qstm, qs') = runState (quadStm stm) s
        (qfrag, qs'') = runState (mapM quadStm userFrags) qs'
        (stms, s') = runState (transform qstm) qs''
        (userFrags', _) = runState (mapM transform qfrag) s'
    return $ stms ++ userFrags

-- constProp :: ([Stm],ReachingDef) -> ([Stm],ReachingDef)
-- {-if n(move const to temp) reches f with no def of n in between-}
-- --stm[n] uses t
-- --in[n] = [n1, n2, n3...] has only one def of t then replace t in stm[n] with const
-- constProp (stms@(s:rest), table) = (constProp' stms table 0 stms,
-- constProp stmAndTable = stmAndTable
--
-- constProp' :: [Stm] -> ReachingDef -> Int -> [Stm] -> [Stm]
-- constProp' stm table i newStm
--   | i == length stm = stm
--   | otherwise =
--       where
--         s = stm !! i
--         used = getRegStm s
--         inDef = fst $ snd (table !! i)
--         numDefs = map (findConst stm  0 0) used --[(num, c)]
--
--
--
-- replaceStm :: Stm -> Temp.Temp -> Int -> Stm
-- replaceStm (MOV (Temp t1) e) t c = MOV (Temp t1) (replaceExp t c e)
-- replaceStm (MOV e (Temp t)) t c = MOV e (CONSTI c)
-- replaceStm (CJUMP cond e1 e2 l1 l2) t c =
--   CJUMP cond (replaceExp t c e1) (replaceExp t c e2) l1 l2
-- replaceStm (EXP (CALL f exps)) t c = EXP (CALL f (map (replaceExp t c) exps))
-- replaceStm stm _ _ = stm
--
-- replaceExp :: Temp.Temp -> Int -> Exp -> Exp
-- replaceExp t c (Temp t) = CONSTI c
-- replaceExp t c (BINEXP bop e1 e2) = BINEXP bop (replaceExp t c e1) (replaceExp t c e2)
-- replaceExp (MEM e i) = MEM (replaceExp t c e) i
-- replaceExp (CALL f exps) = CALL f (map (replaceExp t c) exps)
-- replaceExp _ = []
--
--
-- findConst :: [Stm] -> Int -> Int -> Temp.Temp -> (Int, Int)
-- findConst [] num c t = (num, c) --number of definition of t with the latest one at pos with const i
-- findConst ((MOV (TEMP t) (CONSTI i)):ds) num c t = findConst ds (num + 1) i t
-- findConst (d:ds) num c t = findConst ds num c t
--
-- --get the list of temps used in one statement
-- getRegStm :: Stm -> [Temp.Temp]
-- getRegStm (MOV (Temp t) e) = getRegExp e
-- getRegStm (MOV _ (Temp t)) = [t]
-- getRegStm (CJUMP _ e1 e2 _ _) = concat $ map getRegExp [e1,e2]
-- getRegStm (EXP (CALL _ exps)) = concat $ map getRegExp exps
-- getRegStm _ = []
--
-- getRegExp :: Exp -> [Temp.Temp]
-- getRegExp (Temp t) = [t]
-- getRegExp (BINEXP _ e1 e2) = concat $ map getRegExp [e1,e2]
-- getRegExp (MEM e _) = getRegExp e
-- getRegExp (CALL _ exps) = concat $ map getRegExp exps
-- getRegEXp _ = []

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

genPred :: [DataFlow] -> PredTable
genPred flow = genPred' flow flow []

genPred' :: [DataFlow] -> [DataFlow] -> PredTable -> PredTable
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

--              deftid  in          gkout      init reachingdef
initReachingDef :: [DataFlow] -> (ReachingDef, ReachingDef)
initReachingDef flows = (map takeGK flows, map initReach flows)
    where
        takeGK (M tree g k deftid) = (deftid, (g, k))
        takeGK (E tree deftid) = (deftid, ([], []))
        initReach (M _ _ _ deftid) = (deftid, ([], []))
        initReach (E tree deftid) = (deftid, ([], []))

--                    gk table       current reaching def   pred table  output reaching def
iterateReachingDef :: ReachingDef -> ReachingDef -> PredTable -> ReachingDef
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

genReachingDef :: [DataFlow] -> ReachingDef
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
