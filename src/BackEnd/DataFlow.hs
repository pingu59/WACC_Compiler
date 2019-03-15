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

testQuadfile file = do
    ast <- parseFile file
    ast' <- analyzeAST ast
    let (stm, s) = runState (translate ast') newTranslateState;
        userFrags = map (\(PROC stm _) -> stm) (procFrags s)
        (qstm, qs') = runState (quadStm stm) s
        (qfrag, qs'') = runState (mapM quadStm userFrags) qs'
        -- (stms, s') = runState (transform qstm) qs''
        -- (userFrags', _) = runState (mapM transform qfrag) s'
    return $ qstm --(stms ++ userFrags)

testCSEFile file = do -- only with main
    ast <- parseFile file
    ast' <- analyzeAST ast
    let (stm, s) = runState (translate ast') newTranslateState;
        (qstm, qs') = runState (quadStm stm) s
        (stms, s') = runState (transform qstm) qs'
        (cseout, cseState) = runState (cse stms s') newAState
        transState = trans_ cseState -- get the translate state out
    return cseout

testCopyPropFile file = do -- only with main
    ast <- parseFile file
    ast' <- analyzeAST ast
    let (stm, s) = runState (translate ast') newTranslateState;
        (qstm, qs') = runState (quadStm stm) s
        (stms, s') = runState (transform qstm) qs'
        copy = evalState (copyprop stms) newReachState
    return copy

testConstProp file = do
  ast <- parseFile file
  ast' <- analyzeAST ast
  let (stm, s) = runState (translate ast') newTranslateState;
      (qstm, qs') = runState (quadStm stm) s
      (stms, s') = runState (transform qstm) qs'
      constP = evalState (constProp stms) newReachState
  return constP

quadInterface stm = do
    qstm <- quadStm stm
    stms <- transform qstm
    stms' <- checkLinearAll stms
    return $ stms'

checkLinearAll stms = do
    c <- mapM checkLinearOne stms
    return $ concat c 

checkLinearOne (MOV (MEM e@(ESEQ a r) s) b) = do
    all <- checkLinearAll [a, (MOV (MEM r s) b)]
    return all

checkLinearOne (MOV b (MEM e@(ESEQ a r) s)) = do
    all <- checkLinearAll [a, (MOV b (MEM r s))]
    return all

checkLinearOne x = return [x]

-- constant propagation
constProp :: [Stm] -> State ReachState [Stm]
constProp stms = do
  analyzeReachGK stms
  constPropAll
  state <- get
  return $ constNewStms $ wrappedFlow state

constNewStms :: [ReachFlow] -> [Stm]
constNewStms flows = map tree flows

constPropAll :: State ReachState [()]
constPropAll = do
  state <- get
  mapM (addreTree) (wrappedFlow state)
  mapM constPropOne [0..(length (wrappedFlow state) - 1)]

constPropOne :: Int -> State ReachState ()
constPropOne index = do
  state <- get
  let allFlow = wrappedFlow state
      aFlow = allFlow !! index
      stm = tree aFlow
  case stm of
    --load const from stack
    (MOV (TEMP t) (MEM (CALL (NAME "#memaccess") [(CONSTI size),(CONSTI sp)]) _)) -> do
       findStack index (sp - size)
    otherwise -> do
      let usedTemp = getRegStm stm -- registers used in this stm
      --for usedTemp
      --find number of definition of t with const c in the inDef list
      --if there is only one, replace t with c
      bools <- mapM (findConst index) usedTemp
      --move fold to findConst?? no
      newState <- get
      let newFlow = (wrappedFlow newState) !! index
      folded <- foldStm (tree newFlow)
      case folded of
        Nothing -> do --cannot propagate
          bool <- updateReachFlow $ newFlow {tree = head (reTree newFlow)}
          return ()
        otherwise -> do
          bool <- updateReachFlow $ newFlow {tree = (fromJust folded)}
          return ()


--find the constant on stack
findStack :: Int -> Int -> State ReachState ()
findStack index pos = do
  state <- get
  let aFlow = (wrappedFlow state) !! index
      stm = tree aFlow
      inDef =  fst $ snd ((rd state) !! index)
      --stms = map tree (map (wrappedFlow state !!) inDef) -- stms in inDef
      stms = map tree (wrappedFlow state)
      -- predIndex = snd $ (genReachPred (wrappedFlow state)) !! index
      -- stms = map tree (map (wrappedFlow state !!) predIndex)
      consts = map fromJust $ (filter (/= Nothing) (map (onStack pos) stms))
  case consts of
    [(c, True)] -> do
        let newStm = replaceStack stm c
        bool <- updateReachFlow $ aFlow {tree = newStm}
        return ()
    otherwise -> return ()

replaceStack :: Stm -> Int -> Stm
replaceStack (MOV (TEMP t) (MEM (CALL (NAME "#memaccess") [(CONSTI size), (CONSTI sp)]) _)) c = (MOV (TEMP t) (CONSTI c))
replaceStack s _ = s

onStack :: Int -> Stm -> Maybe (Int,Bool)
onStack pos (MOV (MEM (CALL (NAME "#memaccess") [(CONSTI size), (CONSTI sp)]) _) (CONSTI c))
  | pos == sp - size = Just (c, True) -- find one const
  | otherwise = Nothing
onStack pos (MOV (MEM (CALL (NAME "#memaccess") [(CONSTI size), (CONSTI sp)]) _) e)
  | pos == sp - size = Just (0, False) -- if find another stm that store on stack, cannot propagate
  | otherwise = Nothing
onStack _ _ = Nothing

foldStm :: Stm -> State ReachState (Maybe Stm)
foldStm s@(MOV t e) = do
  let e' =  foldExp e
  case e' of
    Nothing -> return Nothing
    Just (CONSTI c) -> if (check c) then return (Just (MOV t (CONSTI c)))
                        else return Nothing
    otherwise -> return $ Just s
foldStm s = return $ Just s

check c = (c <= (2^31) - 1) && (c >= (negate (2 ^ 31)))

foldExp :: Exp -> Maybe Exp
foldExp (BINEXP PLUS (CONSTI i1) (CONSTI i2)) = Just (CONSTI (i1 + i2))
foldExp (BINEXP MINUS (CONSTI i1) (CONSTI i2)) = Just (CONSTI (i1 - i2))
foldExp (BINEXP MUL (CONSTI i1) (CONSTI i2)) = Just (CONSTI (i1 * i2))
foldExp (BINEXP DIV (CONSTI i1) (CONSTI i2))
  | i2 == 0 = Nothing
  | i1 * i2 > 0 =  Just (CONSTI (div i1 i2))
  | otherwise =  Just (CONSTI (div i1 (negate i2)))
foldExp (BINEXP MOD (CONSTI i1) (CONSTI i2))
  | i2 == 0 = Nothing
  | i1 * i2 > 0 =  Just (CONSTI (mod i1 i2))
  | otherwise =  Just (CONSTI (mod i1 (negate i2)))
foldExp (CALL (NAME "#neg") ((CONSTI i):rest)) = Just (CONSTI (negate i))
foldExp e =  Just e

findConst :: Int -> Temp -> State ReachState Bool
findConst index t = do
  state <- get
  let thisStm = (rd state) !! index
      inDef =  fst $ snd ((rd state) !! index)
      stms = map tree (map (wrappedFlow state !!) inDef) -- stms that can reach  this stm
  case (findConst' stms 0 0 t) of
    (1, c) -> do
      let flows = wrappedFlow state
          aFlow = flows !! index
          newStm = replaceStm' (tree aFlow) t c
          --registers has been replaced with const
      updateReachFlow $ aFlow {tree = newStm}
    otherwise -> return False


findConst' :: [Stm] -> Int -> Int -> Temp.Temp -> (Int, Int)
findConst' [] num c t = (num, c) --number of definition of t with the latest one with const c
findConst' ((MOV (TEMP t1) (CONSTI i)):ds) num c t
  | t1 == t = findConst' ds (num + 1) i t
  | otherwise = findConst' ds num c t
findConst' (d:ds) num c t = findConst' ds num c t

replaceStm' :: Stm -> Temp.Temp -> Int -> Stm
replaceStm' (MOV (TEMP t1) e) t c = MOV (TEMP t1) (replaceExp t c e)
replaceStm' (MOV (MEM e1 i) e2) t c = MOV (MEM e1 i) (replaceExp t c e2)
replaceStm' stm@(MOV e (TEMP t1)) t c
  | t1 == t = MOV e (CONSTI c)
  | otherwise = stm
replaceStm' (CJUMP cond e1 e2 l1 l2) t c =
  CJUMP cond (replaceExp t c e1) (replaceExp t c e2) l1 l2
replaceStm' s@(EXP (CALL f@(NAME n) exps)) t c
  | cannotReplace n = s
  | otherwise = EXP (CALL f (map (replaceExp t c) exps))
replaceStm' stm _ _ = stm

cannotReplace :: Temp.Label -> Bool
cannotReplace n = elem n ["#p_print_int", "#p_check_null_pointer"]

replaceExp :: Temp.Temp -> Int -> Exp -> Exp
replaceExp t c e@(TEMP t1)
  | t == t1 = CONSTI c
  | otherwise = e
replaceExp t c (BINEXP bop e1 e2) = BINEXP bop (replaceExp t c e1) (replaceExp t c e2)
replaceExp t c (MEM e i) = MEM (replaceExp t c e) i
replaceExp t c (CALL f exps) = CALL f (map (replaceExp t c) exps)
replaceExp _ _ e = e

--get the list of temps used in one statement
getRegStm :: Stm -> [Temp.Temp]
getRegStm (MOV (TEMP t) e) = getRegExp e
getRegStm (MOV e1 e2 ) = concatMap getRegExp [e1,e2]
getRegStm (CJUMP _ e1 e2 _ _) = concatMap getRegExp [e1,e2]
getRegStm (EXP (CALL _ exps)) = concatMap getRegExp exps
getRegStm _ = []

getRegExp :: Exp -> [Temp.Temp]
getRegExp (TEMP t) = [t]
getRegExp (BINEXP bop e1 e2) = concatMap getRegExp [e1,e2]
getRegExp (MEM e _) = getRegExp e
getRegExp (CALL _ exps) = concatMap getRegExp exps
getRegExp _ = []




eseq :: State TranslateState (Exp -> Exp)
eseq = do
    t <- Translate.newTemp
    return $ \e -> (ESEQ (MOV (TEMP t) e) (TEMP t))

twoExpr :: Exp -> Exp -> (Exp -> Exp -> a) -> State TranslateState a
twoExpr e1 e2 a = do
    e1' <- quadExp e1
    e2' <- quadExp e2
    if (isBM e1) then do
        eseq1 <- eseq
        if (isBM e2) then do
            eseq2 <- eseq
            return $ a (eseq1 e1') (eseq2 e2')
        else
            return $ a (eseq1 e1') e2'
    else do
        if (isBM e2) then do
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
  if(isBM e1 && isBM e2) then do
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

-- Analyze and put everything in the state
analyzeReachGK :: [Stm] -> State ReachState ()
analyzeReachGK stms = do
    let (gk, gkstate) = runState (wrapReachGK stms) newReachState
        (rdef, pt_) = genReachingDef gk
    put $ gkstate {wrappedFlow = gk, rd = rdef} -- put everything in the state
    return ()

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
wrapOneReachGk m@(M (MOV (TEMP a) _) gen _ _ _) = getReachKill m a gen
wrapOneReachGk x = return x

genReachPred :: [ReachFlow] -> PredTable
genReachPred flow = genReachPred' flow flow []

genReachPred' :: [ReachFlow] -> [ReachFlow] -> PredTable -> PredTable
genReachPred' src [] acc = acc
genReachPred' src ((E (LABEL l) defid _) : rest) acc = genReachPred' src rest (acc ++ [(defid, (searchLable l))])
    where
        searchLable :: String -> [Int]
        searchLable l = (searchLable' src l []) ++ pred
        searchLable' :: [ReachFlow] -> String -> [Int] -> [Int]
        searchLable' [] _ acc = acc
        searchLable' ((E (JUMP _ lables) defid _) : rest) l acc
            | elem l lables = searchLable' rest l (defid:acc)
        searchLable' ((E (CJUMP _ _ _ t f) defid _) : rest) l acc
            | l == t || l == f = searchLable' rest l (defid:acc)
        searchLable' (_:rest) l acc = searchLable' rest l acc
        pred = if (defid /= 0)&&(isNotjump (src!! (defid - 1)))
               then (prevId defid) else []
        isNotjump (E (JUMP _ _) _ _) = False
        isNotjump (E (CJUMP _ _ _ _ _) _ _) = False
        isNotjump _ = True

genReachPred' src ((M _ _ _ defid _) : rest) acc = genReachPred' src rest (acc ++ [(defid, (prevId defid))])
genReachPred' src ((E _ defid _) : rest) acc = genReachPred' src rest (acc ++ [(defid, (prevId defid))])

prevId 0 = []
prevId x = [x - 1]

initReachingDef :: [ReachFlow] -> (ReachingGK , ReachingDef)
initReachingDef flows = (map takeReachGK flows, map initReach flows)
    where
        takeReachGK (M tree g k defid _) = (defid, (g, k))
        takeReachGK (E tree defid _) = (defid, ([], []))
        initReach (M _ _ _ defid _) = (defid, ([], []))
        initReach (E tree defid _) = (defid, ([], []))

iterateReachingDef :: ReachingGK -> ReachingDef -> PredTable -> Int -> ReachingDef
iterateReachingDef gk this pred times
  | this == next || times > (length pred) = this  -- SETTING A HARD LIMIT ON THE NUMBER OF ITERATIONS
  | otherwise = iterateReachingDef gk next pred (times + 1)
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

genReachingDef :: [ReachFlow] -> (ReachingDef, PredTable)
genReachingDef flow = (iterateReachingDef gk init pred 0, pred)
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
    return $ nub $ concatMap (contains target) (wrappedFlow_ state)

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
    put $ state {memFlow_ = containsMem flows, wrappedFlow_ = flows}
    flows' <- mapM wrapOneAGK flows
    state' <- get
    put $ state' {wrappedFlow_ = flows'}
    return flows'

-- wrap stm with AFlow but WITHOUT gen/kill
addOneAGK :: Stm -> State AState AFlow
addOneAGK s = newA s

killMem :: AFlow -> [Exp] -> State AState AFlow
killMem e exps = do
    state <- get
    return $ e {kill_ = filter notInList (memFlow_ state) }
    where
        notInList (MEM a _) = not $ elem a exps

addExpr :: [Exp] -> State AState ()
addExpr exprs = do
    state <- get
    put $ state {allExpr_ = union (allExpr_ state) exprs}

-- Add Gen Kills
wrapOneAGK :: AFlow -> State AState AFlow
wrapOneAGK a@(A (EXP e@(CALL _ exps)) _ _ _ _) = addExpr [e] >> killMem a exps

wrapOneAGK a@(A (MOV (MEM m _) _ ) _ _ _ _) = killMem a [m]
--Pre : t is a temp
wrapOneAGK a@(A (MOV t (CALL _ exps)) _ _ _ _) = do
    state <- get
    cexpr <- containsExpression t
    a' <- killMem a exps
    return $ a' {kill_ = union (kill_ a') cexpr}

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
        (adef, pt) = genADef gk
        rExpr = genReachingExpression adef
    put $ gkstate {re_ = rExpr, trans_ = transtate, pt_ = pt} -- put everything in the state
    cseAll
    state <- get
    return $ unA $ wrappedFlow_ state

cseAll :: State AState [()]
cseAll = do
    state <- get
    mapM (addreTree_) (wrappedFlow_ state)
    mapM cseOne [0..(length (wrappedFlow_ state) - 1)]

addreTree_ :: AFlow -> State AState ()
addreTree_ flow = do
    -- add the tree_ to reTree_, put it back to the state and return
    updateAFlow $ flow {reTree_ = [tree_ flow]}

cseOne :: Int -> State AState ()
cseOne targetNum = do
    state <- get
    let flows = wrappedFlow_ state
        target = flows !! targetNum
        rhs = getRHS (tree_ target)
        reachingExpr = fromJust $ Data.List.lookup targetNum (re_ state) -- PRE: THE TABLE IS COMPLETE
    if (rhs == Nothing || (not $ elem (fromJust rhs) reachingExpr)) then do -- Not a move or Not reachable
        return ()
    else do
        -- find the previously defined exp
        let exprToChange = fromJust rhs
            translateState = trans_ state
            (temp, translateState') = runState (Translate.newTemp) translateState
        exprSources <- findExpr exprToChange targetNum
        mapM (transformSourceExpr temp) exprSources
        transformDstExpr temp target
        return ()

--                  Temp
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
    let flows = wrappedFlow_ state
        defid = defid_ flow
        (prev, aft) = splitAt defid flows
    put $ state {wrappedFlow_ = prev ++ [flow] ++ (drop 1 aft)}
    return ()

-- recursively find the previous instruction until expression not reachable i.e is created
findExpr :: Exp -> Int -> State AState [AFlow]
findExpr expr cur = do
    state <- get
    let reTable = re_ state
    if (not $ elem expr (fromJust $ Data.List.lookup cur reTable)) then
        return [(wrappedFlow_ state) !! cur]
    else do
        let allpred = fromJust $ Data.List.lookup cur (pt_ state)
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

-- copy propagation --
copyprop :: [Stm] -> State ReachState [Stm]
copyprop stms = do
    analyzeReachGK stms
    copyPropAll
    state <- get
    return $ unReach $ wrappedFlow state

copyPropAll :: State ReachState [()]
copyPropAll = do
    state <- get
    mapM (addreTree) (wrappedFlow state)
    mapM copyPropOne [0..(length (wrappedFlow state) - 1)]

copyPropOne :: Int -> State ReachState ()
copyPropOne targetNum = do
    state <- get
    let flows = wrappedFlow state
        targetFlow = flows !! targetNum
        target = tree targetFlow
    case target of
        (MOV (TEMP a) (TEMP b)) -> applyCopyProp targetFlow
        otherwise -> return ()

applyCopyProp :: ReachFlow -> State ReachState ()
applyCopyProp flow = do
    let (MOV (TEMP a) (TEMP b)) = tree flow
        idnum = defid flow
    rf <- reachedFLow idnum
    outs <- mapM (tryCopyProp a) rf
    if (filter (not) outs) /= [] then
        return () -- cannot remove this mov
    else do
        bool <- updateReachFlow $ flow {reTree = []}
        return ()

tryCopyProp :: Int -> Int -> State ReachState Bool
tryCopyProp temp id_ = do
    state <- get
    let thisFlow = (wrappedFlow state) !! id_
    if (usesTemp temp (tree thisFlow)) then do
        canOptimise <- onlyReachOne id_ temp
        if (canOptimise >= 0) then
            subsTemp temp canOptimise id_
        else
            return False -- Indicates this mov cannot be removed
    else
        return True
        where
            usesTemp :: Int -> Stm -> Bool
            usesTemp temp (MOV (MEM b _) a) = ((b == (TEMP temp)) || (a == (TEMP temp)))
            usesTemp temp (MOV _ (TEMP t)) = t == temp
            usesTemp temp (MOV _ (BINEXP _ a b)) = (a == (TEMP temp)) || (b == (TEMP temp))
            usesTemp temp (MOV _ (MEM (TEMP t) _)) = t == temp
            usesTemp temp (CJUMP _ a b _ _) = (a == (TEMP temp)) || (b == (TEMP temp))
            usesTemp temp (EXP (CALL _ exps)) = elem (TEMP temp) exps
            usesTemp temp (MOV _ (CALL _ exps)) = elem (TEMP temp) exps
            usesTemp _ _ = False

            definesTemp :: Int -> Int -> State ReachState Int
            definesTemp temp id_ = do
                state <- get
                let idflow = (wrappedFlow state) !! id_
                case tree idflow of
                    (MOV (TEMP t) (TEMP target)) -> if t == temp then
                                                        return target
                                                    else
                                                        return (-1)
                    otherwise -> return (-1)

            onlyReachOne :: Int -> Temp -> State ReachState Int
            onlyReachOne id_ temp = do
                state <- get
                let (in_, _) = fromJust $ Data.List.lookup id_ (rd state)
                all <- mapM (definesTemp temp) in_
                case filter (>= 0) all of
                    [target] -> return target
                    otherwise -> return (-1)

subsTemp :: Int -> Int -> Int -> State ReachState Bool
subsTemp from to flowid = do
    state <- get
    let flow = (wrappedFlow state) !! flowid
    case tree flow of
        (MOV (MEM a size) b) -> do
            let newa = if a == (TEMP from) then (TEMP to) else a
                newb = if b == (TEMP from) then (TEMP to) else b
            updateReachFlow $ flow {reTree = [(MOV (MEM newa size) newb)]}
        (MOV a (TEMP _)) -> updateReachFlow $ flow {reTree = [(MOV a (TEMP to))]}
        (MOV a (BINEXP rop b c)) -> do
            let newb = if b == (TEMP from) then (TEMP to) else b
                newc = if c == (TEMP from) then (TEMP to) else c
            updateReachFlow $ flow {reTree = [(MOV a (BINEXP rop newb newc))]}
        (MOV a (MEM (TEMP _) size)) -> updateReachFlow $ flow {reTree = [(MOV a (MEM (TEMP to) size))]}
        (CJUMP rop a b t f) -> do
            let newa = if a == (TEMP from) then (TEMP to) else a
                newb = if b == (TEMP from) then (TEMP to) else b
            updateReachFlow $ flow {reTree = [(CJUMP rop newa newb t f)]}
        (EXP (CALL f exps)) -> updateReachFlow $ flow {reTree = [(EXP (CALL f
                                [ if(x == (TEMP from)) then (TEMP to) else x | x <- exps]))]}
        (MOV a (CALL f exps)) -> updateReachFlow $ flow {reTree = [(MOV a (CALL f
                                [ if(x == (TEMP from)) then (TEMP to) else x | x <- exps]))]}

reachedFLow :: Int -> State ReachState [Int]
reachedFLow r = do
    state <- get
    let rd_ = rd state
    return [id_ | (id_, (in_, out_)) <- rd_, elem r in_]

addreTree :: ReachFlow -> State ReachState ()
addreTree flow = do
    bool <- updateReachFlow $ flow {reTree = [tree flow]}
    return ()

unReach :: [ReachFlow] -> [Stm]
unReach flows = concatMap reTree flows

updateReachFlow :: ReachFlow -> State ReachState Bool
updateReachFlow flow = do
    state <- get
    let flows = wrappedFlow state
        defid_ = defid flow
        (prev, aft) = splitAt defid_ flows
    put $ state {wrappedFlow = prev ++ [flow] ++ (drop 1 aft)}
    return True

copyPropStms = [(MOV (TEMP 13) (BINEXP MINUS (TEMP 13) (CONSTI 4))),
                 (MOV (TEMP 16) (TEMP 13)), (MOV (MEM (TEMP 16) 4) (CONSTI 42))]

constPropStms1 = [(MOV (TEMP 10) (CONSTI 1)),
                (MOV (TEMP 12) (CONSTI 2)), (MOV (TEMP 9) (BINEXP MINUS (TEMP 10) (TEMP 12)))]

constPropStms2 = [(MOV (TEMP 10) (CONSTI 1)),
                (MOV (TEMP 12) (TEMP 10)), (MOV (TEMP 9) (CALL (NAME "f") [(TEMP 12), (TEMP 12)])),
                (MOV (MEM (TEMP 12) 4) (TEMP 10))]

constPropStms3 = [(MOV (TEMP 15) (BINEXP PLUS (CONSTI 1) (CONSTI 2))), (MOV (TEMP 16) (BINEXP PLUS (TEMP 15) (CONSTI 2)))]

testCP stms = do
    let out = evalState (constProp stms) newReachState
    putStrLn $ show out

putBackMemAccess :: [Stm] -> [Stm]
putBackMemAccess stms = stms -- putBackMemAccess' (zip [0..] (map (\x -> [x])stms)) stms

-- putBackMemAccess' :: [(Int, [Stm])] -> [Stm] -> [Stm]
-- putBackMemAccess' ref ((MOV (MEM (TEMP t) size) c) : rest)
--   = putBackMemAccess' newref rest
--     where
--         newref = updateRef to [(MOV (MEM sub size) c)]  (updateRef from [] ref)
--         to = (length ref - (length rest))
--         (from, sub) = findTemp (TEMP t) ref
--
-- putBackMemAccess' ref ((MOV c (MEM (TEMP t) size)) : rest)
--   = putBackMemAccess' newref rest
--     where
--         newref =  updateRef to [(MOV c (MEM sub size))]  (updateRef from [] ref)
--         to = (length ref - (length rest))
--         (from, sub) = findTemp (TEMP t) ref
-- putBackMemAccess' ref ((MOV (TEMP t1) b): (EXP (CALL (NAME n) [(TEMP t2)])) : rest)
--     | t1 == t2 = (EXP (CALL (NAME n) [b])) : putBackMemAccess rest
-- putBackMemAccess' ref (x:xs) = x : (putBackMemAccess xs)
-- putBackMemAccess' ref [] = concatMap snd ref

updateRef i stm ref
    | i > 0 = [ if num == i then (num, stm) else (num, x) | (num , x) <- ref]
    | otherwise = ref

findTemp :: Exp -> [(Int, [Stm])] -> (Int, Exp)
findTemp temp [] = undefined
findTemp temp ((num, [(EXP (CALL (NAME "malloc") [a, b]))] ):xs)
    | b == temp = (-1, b) -- should not delete
findTemp temp ((num, [(MOV a b)]):xs)
    | a == temp = (num, b)
findTemp temp (x : xs) = findTemp temp xs
