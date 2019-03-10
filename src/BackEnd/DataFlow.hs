module BackEnd.DataFlow where
import BackEnd.Canon
import BackEnd.Translate as Translate
import BackEnd.IR as IR
import Control.Monad.State.Lazy
import BackEnd.Frame
import FrontEnd.Parser
import FrontEnd.SemanticAnalyzer
import BackEnd.GenKill
import Data.HashMap as HashMap hiding (map, (\\), union, filter)
import Data.Maybe
import Data.List
import BackEnd.Temp as Temp

{-
1. take translation from translate and change them to quadruples -- done!
2. feed the quadruples into canon -- done ?
3. take the canonical quadruples and perform analysis --done
4. transform
-}

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

testQuadfile file = do
    ast <- parseFile file
    ast' <- analyzeAST ast
    let (stm, s) = runState (translate ast') newTranslateState;
        userFrags = map (\(PROC stm _) -> stm) (procFrags s)
        (qstm, qs') = runState (quadStm stm) s
        (qfrag, qs'') = runState (mapM quadStm userFrags) qs'
        (stms, s') = runState (transform qstm) qs''
        (userFrags', _) = runState (mapM transform qfrag) s'
    return $ (stms ++ userFrags)

testReachingExprFile file = do
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
        (adef, _) = genADef (gkmain ++ concat gkuser)
        rExpr = genReachingExpression adef
    return $ rExpr

testCSEFile file = do -- only with main
    ast <- parseFile file
    ast' <- analyzeAST ast
    let (stm, s) = runState (translate ast') newTranslateState;
        (qstm, qs') = runState (quadStm stm) s
        (stms, s') = runState (transform qstm) qs'
        (cseout, cseState) = runState (cse stms s') newAState 
        transState = trans cseState -- get the translate state out
    return cseout

-- constProp :: ([Stm],ReachingDef) -> ([Stm],ReachingDef)
-- {-if n(move const to temp) reches f with no def of n in between-}
-- --stm[n] uses t
-- --in[n] = [n1, n2, n3...] has only one def of t then replace t in stm[n] with const
-- constProp (stms, table) = (newStm, newTable)
--   where
--     newStm = constProp' stms table 0 []
--     newTable = do
--       flow <- wrapReachGK newStm
--       return $ genReachingDef flow
-- constProp stmAndTable = stmAndTable

constProp' :: [Stm] -> ReachingDef -> Int -> [Stm] -> [Stm]
constProp' stm table i newStm
  | i == length stm = newStm
  | otherwise = constProp' stm table (i + 1) (newStm ++ [new])
      where
        s = stm !! i
        used = getRegStm s --list of registers used in s
        inDef = fst $ snd (table !! i) --register definition reaches s
        --number of definition of t with const c
        numDefs = map (findConst stm  0 0) used --[(num, c)]
        new = replaceStm s used numDefs

replaceStm :: Stm -> [Temp.Temp] -> [(Int, Int)] -> Stm
replaceStm stm [] [] = stm
replaceStm stm (t:ts) ((1, c):rest) = replaceStm stm' ts rest
    where
      stm' = replaceStm' stm t c
replaceStm stm _ _ = stm

replaceStm' :: Stm -> Temp.Temp -> Int -> Stm
replaceStm' (MOV (TEMP t1) e) t c = MOV (TEMP t1) (replaceExp t c e)
replaceStm' stm@(MOV e (TEMP t1)) t c
  | t1 == t = MOV e (CONSTI c)
  | otherwise = stm
replaceStm' (CJUMP cond e1 e2 l1 l2) t c =
  CJUMP cond (replaceExp t c e1) (replaceExp t c e2) l1 l2
replaceStm' (EXP (CALL f exps)) t c = EXP (CALL f (map (replaceExp t c) exps))
replaceStm' stm _ _ = stm

replaceExp :: Temp.Temp -> Int -> Exp -> Exp
replaceExp t c e@(TEMP t1)
  | t == t1 = CONSTI c
  | otherwise = e
replaceExp t c (BINEXP bop e1 e2) = BINEXP bop (replaceExp t c e1) (replaceExp t c e2)
replaceExp t c (MEM e i) = MEM (replaceExp t c e) i
replaceExp t c (CALL f exps) = CALL f (map (replaceExp t c) exps)
replaceExp _ _ e = e


findConst :: [Stm] -> Int -> Int -> Temp.Temp -> (Int, Int)
findConst [] num c t = (num, c) --number of definition of t with the latest one at pos with const c
findConst ((MOV (TEMP t1) (CONSTI i)):ds) num c t
  | t1 == t = findConst ds (num + 1) i t
  | otherwise = findConst ds num c t
findConst (d:ds) num c t = findConst ds num c t

--get the list of temps used in one statement
getRegStm :: Stm -> [Temp.Temp]
getRegStm (MOV (TEMP t) e) = getRegExp e
getRegStm (MOV _ (TEMP t)) = [t]
getRegStm (CJUMP _ e1 e2 _ _) = concat $ map getRegExp [e1,e2]
getRegStm (EXP (CALL _ exps)) = concat $ map getRegExp exps
getRegStm _ = []

getRegExp :: Exp -> [Temp.Temp]
getRegExp (TEMP t) = [t]
getRegExp (BINEXP _ e1 e2) = concat $ map getRegExp [e1,e2]
getRegExp (MEM e _) = getRegExp e
getRegExp (CALL _ exps) = concat $ map getRegExp exps
getRegEXp _ = []

eseq :: State TranslateState (Exp -> Exp)
eseq = do
    t <- Translate.newTemp
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
genReachPred' src ((E (LABEL l) defid) : rest) acc = genReachPred' src rest (acc ++ [(defid, (searchLable l))])
    where
        searchLable :: String -> [Int]
        searchLable l = (searchLable' src l []) ++ pred
        searchLable' :: [ReachFlow] -> String -> [Int] -> [Int]
        searchLable' [] _ acc = acc
        searchLable' ((E (JUMP _ lables) defid) : rest) l acc
            | elem l lables = searchLable' rest l (defid:acc)
        searchLable' ((E (CJUMP _ _ _ t f) defid) : rest) l acc
            | l == t || l == f = searchLable' rest l (defid:acc)
        searchLable' (_:rest) l acc = searchLable' rest l acc
        pred = if (defid /= 0)&&(isNotjump (src!! (defid - 1)))
               then (prevId defid) else []
        isNotjump (E (JUMP _ _) _) = False
        isNotjump (E (CJUMP _ _ _ _ _) _) = False
        isNotjump _ = True

genReachPred' src ((M _ _ _ defid) : rest) acc = genReachPred' src rest (acc ++ [(defid, (prevId defid))])
genReachPred' src ((E _ defid) : rest) acc = genReachPred' src rest (acc ++ [(defid, (prevId defid))])

prevId 0 = []
prevId x = [x - 1]

initReachingDef :: [ReachFlow] -> (ReachingGK , ReachingDef)
initReachingDef flows = (map takeReachGK flows, map initReach flows)
    where
        takeReachGK (M tree g k defid) = (defid, (g, k))
        takeReachGK (E tree defid) = (defid, ([], []))
        initReach (M _ _ _ defid) = (defid, ([], []))
        initReach (E tree defid) = (defid, ([], []))

iterateReachingDef :: ReachingGK -> ReachingDef -> PredTable -> ReachingDef
iterateReachingDef gk this pred
  | this == next = this
  | otherwise = iterateReachingDef gk next pred
  where
    next = iterateOnce this []
    iterateOnce :: ReachingDef -> ReachingDef ->  ReachingDef
    iterateOnce [] acc = acc
    iterateOnce ((defid, (in_, out_)):remain) acc = iterateOnce remain (acc ++ [updated])
        where
            updated = (defid, (newIn, newOut))
            predThis = fromJust ((Data.List.lookup) defid pred)
            predOut = map fromJust $ (filter (/= Nothing) (map (\x -> Data.List.lookup x this) predThis))
            newIn = if predOut == [] then [] else foldl1 union (map snd predOut)
            (gen, kill) = fromJust $ (Data.List.lookup) defid gk
            newOut = union  gen (in_ \\ kill)

genReachingDef :: [ReachFlow] -> ReachingDef
genReachingDef flow = iterateReachingDef gk init pred
    where
        (gk, init) = initReachingDef flow
        pred = genReachPred flow

reachingDefSample = [MOV (TEMP 1) (CONSTI 5), MOV (TEMP 2) (CONSTI 1), LABEL "L1",
                     CJUMP IR.LT (TEMP 2) (TEMP 1) "L2" "LNEXT", LABEL "LNEXT",
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

containsExpression :: Exp -> State AState [Exp]
containsExpression target = do
    state <- get 
    return $ nub $ concatMap (contains target) (wrappedFlow state)

containsMem :: [AFlow] -> [Exp]
containsMem flows = concatMap containsOneMem flows

containsOneMem :: AFlow -> [Exp]
containsOneMem (A (MOV a e@(MEM b _)) _ _ _ _) = [e]
containsOneMem (A (MOV e@(MEM a _) b) _ _ _ _) = [e]
containsOneMem _ = []

contains :: Exp -> AFlow -> [Exp]
--s1
contains target (A (MOV a expr@(BINEXP _ b c )) _ _ _ _)
    | b == target || c == target = [expr]
--s5
contains target (A (MOV a expr@(MEM b _)) _ _ _ _)
    | b == target = [expr]
--s9
contains target (A (MOV a expr@(CALL e es)) _ _ _ _)
    | elem target (e:es) = [expr]
--s8
contains target (A (EXP expr@(CALL e es)) _ _ _ _)
    | elem target (e:es) = [expr]
--s6
contains target (A (MOV expr@(MEM a _) b) _ _ _ _)
    | a == target = [expr]

--s3
contains _ _ = []

wrapAGK :: [Stm] -> State AState [AFlow]
wrapAGK stms = do
    flows <- mapM addOneAGK stms
    state <- get
    put $ state {memFlow = containsMem flows, wrappedFlow = flows}
    flows' <- mapM wrapOneAGK flows
    state' <- get
    put $ state' {wrappedFlow = flows'}

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
wrapOneAGK a@(A (EXP e@(CALL _ _)) _ _ _ _) = addExpr [e] >> killMem a

wrapOneAGK a@(A (MOV (MEM _ _) _ ) _ _ _ _) = killMem a
--Pre : t is a temp
wrapOneAGK a@(A (MOV t (CALL _ _)) _ _ _ _) = do
    state <- get
    cexpr <- containsExpression t
    return $ a {kill_ = union (memFlow state) cexpr}

wrapOneAGK a@(A (MOV t b) _ _ _ _) = do
    cexpr <- containsExpression t
    return $ a {kill_ = cexpr, gen_ = ([b]\\cexpr)}

wrapOneAGK x = return x

genAPred :: [AFlow] -> PredTable
genAPred flow = genAPred' flow flow []

genAPred' :: [AFlow] -> [AFlow] -> PredTable -> PredTable
genAPred' src [] acc = acc
genAPred' src ((A (LABEL l) _ _ defid _) : rest) acc = genAPred' src rest (acc ++ [(defid, (searchLable l))])
    where
        searchLable :: String -> [Int]
        searchLable l = (searchLable' src l []) ++ pred
        searchLable' :: [AFlow] -> String -> [Int] -> [Int]
        searchLable' [] _ acc = acc
        searchLable' ((A (JUMP _ lables) _ _ defid _) : rest) l acc
            | elem l lables = searchLable' rest l (defid:acc)
        searchLable' ((A (CJUMP _ _ _ t f) _ _ defid _) : rest) l acc
            | l == t || l == f = searchLable' rest l (defid:acc)
        searchLable' (_:rest) l acc = searchLable' rest l acc
        pred = if (defid /= 0)&&(isNotjump (src!! (defid - 1)))
               then (prevId defid) else []
        isNotjump (A (JUMP _ _) _ _ _ _) = False
        isNotjump (A (CJUMP _ _ _ _ _) _ _ _ _) = False
        isNotjump _ = True

genAPred' src ((A _ _ _ defid _) : rest) acc = genAPred' src rest (acc ++ [(defid, (prevId defid))])

initADef :: [AFlow] -> (AGK, ADef)
initADef flows = (map takeAGK flows, map initA flows)
    where
        takeAGK (A tree g k defid _) = (defid, (g, k))
        initA (A _ _ _ defid _) = (defid, ([], []))

iterateADef :: AGK -> ADef -> PredTable -> ADef
iterateADef gk this pred
  | this == next = this
  | otherwise = iterateADef gk next pred
  where
    next = iterateOnce this []
    iterateOnce :: ADef -> ADef -> ADef
    iterateOnce [] acc = acc
    iterateOnce ((defid, (in_, out_)):remain) acc = iterateOnce remain (acc ++ [updated])
        where
            updated = (defid, (newIn, newOut))
            predThis = fromJust ((Data.List.lookup) defid pred)
            predOut = map fromJust $ (filter (/= Nothing) (map (\x -> Data.List.lookup x this) predThis))
            newIn = if predOut == [] then [] else foldl1 intersect (map snd predOut)
            (gen, kill) = fromJust $ (Data.List.lookup) defid gk
            newOut = union gen (in_ \\ kill)

genADef :: [AFlow] -> (ADef, PredTable)
genADef flow = (iterateADef gk init pred, pred)
    where
        (gk, init) = initADef flow
        pred = genAPred flow

genReachingExpression :: ADef -> ReachingExpr
genReachingExpression adef = map reachingOneExpression adef

reachingOneExpression :: (Int, ([Exp], [Exp])) -> (Int, [Exp])
reachingOneExpression (defid, (in_, out_))
    = (defid, subset)
    where
        subset = nub $ concatMap (genOneReachable) (intersect in_ out_)
        genOneReachable :: Exp -> [Exp]
        genOneReachable a@(BINEXP _ _ _) = [a]
        -- genOneReachable a@(BINEXP _ b c) = [a, b, c]
        genOneReachable a@(MEM b _) = [a]
        -- genOneReachable a@(MEM b _) = [b]
        genOneReachable _ = fail "EXPRESSION CONTAINS NOT ALLOWED GENS"

-- COMMON-SUBEXPRESSION ELIMINATION
-- NEED TO CARRY TRANSLATE STATE REGISTER INFORMATION 
-- REWRITE the translate state information after use ***
-- pre: apply this on each frag **separately**
cse :: [Stm] -> TranslateState -> State AState [Stm]
cse stms transtate = do
    let (gk, gkstate) = runState (wrapAGK stms) newAState
        (adef, pt_) = genADef gk
        rExpr = genReachingExpression adef
    put $ gkstate {re = rExpr, trans = transtate, pt = pt_} -- put everything in the state
    cseAll
    state <- get
    return $ unA $ wrappedFlow state

cseAll :: State AState [()]
cseAll = do
    state <- get
    mapM (addreTree) (wrappedFlow state)
    mapM cseOne [0..(length (wrappedFlow state) - 1)]

addreTree :: AFlow -> State AState ()
addreTree flow = do
    -- add the tree_ to reTree_, put it back to the state and return
    updateAFlow $ flow {reTree_ = [tree_ flow]}

cseOne :: Int -> State AState ()
cseOne targetNum = do 
    state <- get 
    let flows = wrappedFlow state
        target = flows !! targetNum
        rhs = getRHS (tree_ target)
        reachingExpr = fromJust $ Data.List.lookup targetNum (re state) -- PRE: THE TABLE IS COMPLETE
    if (rhs == Nothing || (not $ elem (fromJust rhs) reachingExpr)) then do -- Not a move or Not reachable
        return ()
    else do
        -- find the previously defined exp
        let exprToChange = fromJust rhs
            translateState = trans state
            (temp, translateState') = runState (Translate.newTemp) translateState 
        exprSources <- findExpr exprToChange targetNum
        mapM (transformSourceExpr temp) exprSources
        transformDstExpr temp target
        return ()

--                     Temp 
transformDstExpr :: Int -> AFlow -> State AState ()
transformDstExpr temp (A tree gen kill defid ((MOV a b):res)) = do
    let newDst = (A tree gen kill defid ((MOV a (TEMP temp)):res))
    updateAFlow newDst

transformSourceExpr :: Int -> AFlow -> State AState ()
transformSourceExpr temp (A tree gen kill defid ((MOV a b):res)) = do
    let newSource = (A tree gen kill defid ((MOV (TEMP temp) b):(MOV a (TEMP temp)):res))
    updateAFlow newSource

updateAFlow :: AFlow -> State AState ()
updateAFlow flow = do        
    state <- get
    let flows = wrappedFlow state
        defid = defid_ flow
        (prev, aft) = splitAt defid flows
    put $ state {wrappedFlow = prev ++ [flow] ++ (drop 1 aft)}
    return ()

-- recursively find the previous instruction until expression not reachable i.e is created
findExpr :: Exp -> Int -> State AState [AFlow]
findExpr expr cur = do
    state <- get
    let reTable = re state
    if (not $ elem expr (fromJust $ Data.List.lookup cur reTable)) then
        return [(wrappedFlow state) !! cur]
    else do
        let allpred = fromJust $ Data.List.lookup cur (pt state)
        allSource <- mapM (findExpr expr) allpred
        if allSource == [] then 
            fail "SHOULD HAVE AT LEAST ONE SOURCE"
        else
            return $ concat allSource

getRHS :: Stm -> Maybe Exp
getRHS (MOV _ b@(BINEXP _ _ _)) = Just b
getRHS _ = Nothing
        
unA :: [AFlow] -> [Stm]
unA flows = concatMap reTree_ flows
