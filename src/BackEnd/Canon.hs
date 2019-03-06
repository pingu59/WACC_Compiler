module BackEnd.Canon where

import Prelude hiding (EQ)
import Control.Monad.State
import Data.HashMap as HashMap hiding (map, filter)
import FrontEnd.Parser
import FrontEnd.SemanticAnalyzer
import BackEnd.Translate as Translate
import qualified BackEnd.Temp as Temp
import BackEnd.IR
import Data.List hiding(insert)
import BackEnd.Frame as Frame

{- Note
   -----------------------------------------------------------------------------
   Canon is used for transforming the IR tree to enable munching (instruction
   selection).
   The transform includes mainly of:
   1. linearize
   2. basicBlocks
   3. traceSchedule

  The design is inspired by Modern Compiler Implementation in ML.
-}


-- Main function for transforming IR tree 
transform :: Stm -> State TranslateState [Stm]
transform stm = do
  stms <- linearize stm
  blocks <- basicBlocks stms
  let stms = traceSchedule $ fst blocks
  fla <- mapM flat stms
  return $ filter (/= NOP)(concat fla)

transform' :: Stm -> State TranslateState [[Stm]]
transform' stm = do
  stms <- linearize stm
  (stms', _) <- basicBlocks stms
  return stms'

flat :: Stm -> State TranslateState [Stm]
flat (MOV e1 e2) = do
  (i1, t1) <- flat' e1
  (i2, t2) <- flat' e2
  return $ i1 ++ i2 ++ [MOV t1 t2]

flat (SEQ s1 s2) = do
  i1 <- flat s1
  i2 <- flat s2
  return $ i1 ++ i2

flat other = return [other]

flat' :: Exp -> State TranslateState ([Stm], Exp)
flat' exp@(BINEXP bop e1 e2@(BINEXP bop2 e21 e22)) = do
  if isOneLayer e1 && isOneLayer e2
  then return ([NOP], exp)
  else do
    ttotal <- newTemp
    (stm2 , te2) <- flat' e2 
    let ret = stm2 ++ [MOV (TEMP ttotal) (BINEXP bop e1 te2)]
    return ( ret, (TEMP ttotal))
flat' x = return ([NOP], x)

{- Note
   ----------------------------------------------------------------------------
   linearize: statements in ESEQ (side effects of expression) are lifted up and
              function call values are reserved in new temporaries, then the
              IR tree is linearized into list of stm
-}
linearize :: Stm -> State TranslateState [Stm]
linearize stm = do
  stm' <- doStm stm
  return $ filter (/= NOP) $ linear stm' []
  where  linear :: Stm -> [Stm] -> [Stm]
         linear (SEQ a b) list = linear a (linear b list)
         linear s list = s:list

{- Note
  ------------------------------------------------------------------------------
  basicBlocks : organize list of statements into basic blocks.
                A basic block is a list of statements such that
                1. It starts with a label
                2. It ends with a jump or a conditional jump
                3. There's no labels or jumps in between
-}
basicBlocks :: [Stm] -> State TranslateState ([[Stm]], Temp.Label)
basicBlocks [] = do
  label <- newControlLabel
  return $ ([[LABEL label]], label)
basicBlocks (l@(LABEL label):rest) = do
  let { (block, rest') = break (\e -> isEND e) rest }
  if rest' == [] || isLABEL (head rest')
  then do
    (restBlock1, nextLabel1) <- basicBlocks rest'
    return (((l:block) ++ [JUMP (CONSTI 1) [nextLabel1]]):restBlock1, label)
  else do
    (restBlock2, _) <- basicBlocks $ tail rest'
    return (((l:block) ++ [head rest']):restBlock2, label)
 where isJUMP (JUMP _ _) = True
       isJUMP _ = False
       isCJUMP (CJUMP _ _ _ _ _) = True
       isCJUMP _ = False
       isLABEL (LABEL _) = True
       isLABEL _ = False
       isEND e = (isJUMP e) || (isCJUMP e) || (isLABEL e)
basicBlocks stms@(stm:rest) = do
  label <- newControlLabel
  basicBlocks ((LABEL label):stms)

bLabel ((LABEL label):_) = label

{- Note
   -----------------------------------------------------------------------------
   traceSchedule : Take a list of basic blocks and reorder them.
                   Reorder them so that a block that ends with a conditional
                   jump is followed immediately by a block that starts with the
                   false label of the jump, thereby simpifying instruction
                   selection for conditional jump.
-}

traceSchedule :: [[Stm]] -> [Stm]
traceSchedule blocks = traceSchedule' blocks blockTable markTable
  where markTable = HashMap.empty
        blockTable = foldl addBlock HashMap.empty blocks
        addBlock acc b = insert (bLabel b) b acc

traceSchedule' [] _ _ = []
traceSchedule' (block:rest) blockTable markTable
 = trace ++ traceSchedule' rest' blockTable markTable'
 where (trace, markTable') =
         traceSchedule'' block blockTable markTable
       rest' =
         filter (\b -> not $ member (bLabel b) markTable') rest

traceSchedule'' block@((LABEL label):rest) blockTable markTable
  | unMarkedSucc /= [] = (block ++ trace, markTable'')
  | otherwise = (block, markTable')
  where nextBlock = blockTable ! (head unMarkedSucc)
        markTable' = insert label 1 markTable
        unMarkedSucc =
          filter (\l -> not $ member l markTable') (succs block)
        (trace, markTable'') =
          traceSchedule'' nextBlock blockTable markTable'
        succs block =
          case last block of
            LABEL _ -> []
            JUMP _ labels -> labels
            CJUMP _ _ _ label1 label2 -> [label2, label1]


-- test whether two statements commute or not
commute :: Exp -> Stm -> Bool
commute (CONSTI _) _ = True
commute (CONSTC _) _ = True
commute (NAME _) _ = True
commute _ (EXP (CONSTI _)) = True
commute _ (EXP (CONSTC _)) = True
commute _ NOP = True
commute _ _ = False

connect (EXP (CONSTI _)) x = x
connect (EXP (CONSTC _)) x = x
connect x (EXP (CONSTI _)) = x
connect x (EXP (CONSTC _)) = x
connect x y = SEQ x y

isESEQ :: Exp -> Bool
isESEQ (ESEQ _ _) = True
isESEQ _ = False

reorder :: [Exp] -> State TranslateState (Stm, [Exp])
reorder (exp@(CALL (NAME n) _):rest)
 | "#" `isPrefixOf` n = do
   (stm, exps) <- reorder rest
   return (stm, (exp:exps))
reorder (exp@(CALL _ _):rest) = do
  temp <- newTemp
  reorder ((ESEQ (MOV (TEMP temp) exp) (TEMP temp)):rest)
reorder (exp:rest) = do
  (stm', exps') <- doExp exp
  (stm2', exps2') <- reorder rest
  if commute exps' stm2'
  then return (SEQ stm' stm2', (exps':exps2'))
  else newTemp >>= \temp ->
       return (connect stm' (connect (MOV (TEMP temp) exps') stm2'),
               (TEMP temp):exps2')
reorder [] = return (NOP, [])


reorderStm :: [Exp] -> ([Exp] -> Stm) -> State TranslateState Stm
reorderStm exps build = do
  (stm, exps') <- reorder  exps
  return $ connect stm (build  exps')

reorderExp :: [Exp] -> ([Exp] -> Exp) -> State TranslateState (Stm, Exp)
reorderExp exps build = do
  (stm', exps') <- reorder exps
  return (stm', build exps')


doStm :: Stm -> State TranslateState Stm

doStm p@(PUSHREGS _) = return p

doStm p@(POPREGS _) = return p

doStm (MOV (TEMP t) (CALL (NAME f) es))
  = reorderStm es (\es -> MOV (TEMP t) (CALL (NAME f) es))

doStm (MOV (MEM e s) (CALL (NAME f) es))
  = reorderStm (e:es) (\(e:es) -> MOV (MEM e s) (CALL (NAME f) es))

doStm (MOV (TEMP t) (CALL e es)) = undefined
  -- = reorderStm (e:es) (\(e:es) -> MOV (TEMP t) (CALL e es))

doStm (MOV (TEMP t) b)
  = reorderStm [b] (\(b:_) -> MOV (TEMP t) b)

doStm stm@(MOV (MEM e@(BINEXP bop e1 e2) s) b)
  | isOneLayer e1 && isOneLayer e2 && isOneLayer b =
      return stm

doStm stm@(MOV (MEM (TEMP t) size) (ESEQ s e)) = do
  s' <- doStm s
  reorderStm [e] (\(e:_) -> SEQ s' (MOV (MEM (TEMP t) size) e))

doStm stm@(MOV (MEM e s) b) = do
  reorderStm [e, b] (\(e:b_) -> MOV (MEM e s) b)

doStm (MOV (ESEQ s e) b)
  = doStm (SEQ s (MOV e b))

doStm (JUMP e labels)
  = reorderStm [e] (\(e:_) -> JUMP e labels)

doStm (CJUMP rop e1 e2 label1 label2)
  = reorderStm [e1, e2] (\(e1:e2:_) -> CJUMP rop e1 e2 label1 label2)

doStm (SEQ stm1 stm2) = do
  stm1' <- doStm stm1
  stm2' <- doStm stm2
  return $ SEQ stm1' stm2'

doStm (EXP (CALL (NAME f) es))
  = reorderStm es (\es -> EXP (CALL (NAME f) es))

doStm (EXP (CALL e es))
  = reorderStm (e:es) (\(e:es) -> EXP (CALL e es))
doStm (EXP e)
  = reorderStm [e] (\(e:_) -> EXP e)

doStm stm = return stm

isOneLayer :: Exp -> Bool
isOneLayer (CONSTI _) = True
isOneLayer (CONSTC _) = True
isOneLayer (TEMP _) = True
isOneLayer (MEM _ _) = True
isOneLayer (NAME _) = True
isOneLayer e = False

doExp :: Exp -> State TranslateState (Stm, Exp)
doExp exp@(MEM e@(BINEXP bop e1 e2) s) = do
  if isOneLayer e1 && isOneLayer e2
  then return (NOP, exp)
  else reorderExp [e] (\(e:_) -> MEM e s)

doExp exp@(BINEXP bop e1 e2) = do
  if isOneLayer e1 && isOneLayer e2
  then return (NOP, exp)
  else reorderExp [e1, e2] (\(e1:e2:_) -> BINEXP bop e1 e2)

doExp (MEM e s)
  = reorderExp [e] (\(e:_) -> MEM e s)

doExp (CALL (NAME f) es)
  = reorderExp es (\es -> CALL (NAME f) es)

doExp (CALL e es)
  = reorderExp (e:es) (\(e:es) -> CALL e es)

doExp (ESEQ stm e) = do
  stm' <- doStm stm
  (stm'', e') <- doExp e
  return (SEQ stm' stm'', e')

doExp e = reorderExp [] (\_ -> e)


-- Utility for Testing
testCanonFile :: String -> IO [Stm]
testCanonFile file = do
  ast <- parseFile file
  ast' <- analyzeAST ast
  let (stm, s) = runState (Translate.translate ast') Translate.newTranslateState;
      userFrags = map (\(Frame.PROC stm _) -> stm) (Translate.procFrags s)
      (stms, s') = runState (transform stm) s
      (userFrags') = evalState (mapM transform userFrags) s'
  return $ stms ++ concat userFrags'

testBasicBlocksFile :: String -> IO [[Stm]]
testBasicBlocksFile file = do
  ast <- parseFile file
  ast' <- analyzeAST ast
  let { (stm, s) = runState (Translate.translate ast') Translate.newTranslateState;
        stms = evalState (transform' stm) s }
  return stms

testLinearizeFile :: String -> IO [Stm]
testLinearizeFile file = do
  ast <- parseFile file
  ast' <- analyzeAST ast
  let { (stm, s) = runState (Translate.translate ast') Translate.newTranslateState;
        stms = evalState (linearize stm) s }
  return stms


testCanon :: Stm -> IO [Stm]
testCanon stm = do
  let { (trace, s) = runState (transform stm) newTranslateState }
  return trace


testDoStm :: Stm -> IO Stm
testDoStm stm = do
  let { (stm', s) = runState (doStm stm) newTranslateState }
  return stm'

testLinearize :: Stm -> IO [Stm]
testLinearize stm = do
  let { (stm', s) = runState (linearize stm) newTranslateState }
  return $ filter (/= NOP) stm'

testBasicBlocks :: [Stm] -> IO [[Stm]]
testBasicBlocks stms = do
  let { (blocks, s) =
        runState (basicBlocks stms >>= \(bs,_) -> return bs) newTranslateState }
  return blocks

testDoExp :: Exp -> IO Exp
testDoExp exp = do
  let { ((stm,exp'), s) = runState (doExp exp) newTranslateState }
  return $ ESEQ stm exp'
