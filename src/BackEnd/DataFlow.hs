module BackEnd.DataFlow where
import BackEnd.Canon
import BackEnd.Translate
import BackEnd.IR 
import Control.Monad.State.Lazy
import BackEnd.Frame
import FrontEnd.Parser
import FrontEnd.SemanticAnalyzer

{-
1. take translation from translate and change them to quadruples
2. feed the quadruples into canon
3. take the canonical quadruples and perform analysis
-}

isBM :: Exp -> Bool
isBM (MEM _ _) = True
isBM (BINEXP _ _ _) = True
isBM _ = False

testQuadFile :: String -> IO [Stm]
testQuadFile file = do
  ast <- parseFile file
  ast' <- analyzeAST ast
  let (stm, s) = runState (translate ast') newTranslateState;
      userFrags = map (\(PROC stm _) -> stm) (procFrags s)
      (stms, s') = runState (transform stm) s
      (userFrags', qs) = runState (mapM transform qfrag) s'
      (qstm, qs') = runState (mapM quadStm stms) qs
      (qfrag, qs'') = runState (mapM quadStm $ concat userFrags') qs'
 --     cqstm = evalState (mapM transform (qstm ++ qfrag)) qs''
  --return $ stms ++ concat userFrags'
  return $ qstm ++ qfrag -- concat cqstm

eseq :: State TranslateState (Exp -> Exp)
eseq = do 
    t <- newTemp
    return $ \e -> (ESEQ (MOV (TEMP t) e) (TEMP t))

twoExpr :: Exp -> Exp -> (Exp -> Exp -> a) -> State TranslateState a 
twoExpr e1 e2 a = do
    return $ a e1 e2
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