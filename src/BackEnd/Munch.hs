module BackEnd.Munch where

import Data.Maybe
import Data.List
import Control.Monad.State.Lazy
import qualified Data.Set as Set

import FrontEnd.Parser
import FrontEnd.SemanticAnalyzer
import BackEnd.Instructions as ARM
import BackEnd.IR as IR
import BackEnd.Assem as ASSEM
import BackEnd.Temp hiding (newTemp, newDataLabel)
import BackEnd.Translate as Translate
import BackEnd.Frame as Frame
import BackEnd.Builtin
import BackEnd.Canon as C hiding (newTemp)
--how to know scope ?? when frame is changed ???
--TODO : difference between b and bl ??
-- REGISTER SAVE??
-- STRING ASSIGNMENT?
-- how to know if something is to store on the stack? -- after ir is fixed, add sp cases of minus
bopToCBS :: BOp ->  Maybe (Suffix -> Cond -> Calc)
bopToCBS bop
  = lookup bop [(IR.PLUS, ARM.ADD), (IR.AND, ARM.AND), (IR.OR, ARM.ORR),
            (IR.LSHIFT, ARM.LSL), (IR.RSHIFT, ARM.LSR), (IR.MINUS, ARM.SUB)]

justret e = do
  (i, t) <- munchExp e
  return (i , t)

munchExp :: Exp -> State TranslateState ([ASSEM.Instr], Temp)
munchExp (CALL (NAME "#retVal") [e]) = justret e

munchExp (CALL (NAME "#memaccess") [CONSTI i]) = do
  t <- newTemp
  return ([IOPER {assem = CBS_ (ADD NoSuffix AL) (RTEMP t) SP (IMM i),
                 src = [13], dst = [t], jump = []}], t)

munchExp (CALL (NAME "malloc") [CONSTI i]) = do
  t <-newTemp
  let ldr = IMOV { assem = S_ (LDR W AL) (R0) (NUM (i)),
                  src = [], dst = [0]}
      move = IMOV { assem = MC_ (ARM.MOV AL) (RTEMP t) (R R0),
                    src = [t], dst = [0] }
  return ([ldr, ljump_to_label "malloc", move], dummy)

munchExp (CALL (NAME "#arrayelem") [(CONSTI size), ident, pos]) = do
  (ii, it) <- munchExp ident
  (pi, pt) <- munchExp pos
  let op = if size == 1 then (R (RTEMP pt)) else (LSL_ (RTEMP pt) 2)
      m0 = move_to_r pt 0
      m1 = move_to_r it 1
      bl = IOPER {assem = BRANCH_ (BL AL) (L_ "p_check_array_bounds"),
                  src = [0, 1], dst = [], jump = ["p_check_array_bounds"]}
      skiplen = IOPER {assem = CBS_ (ADD NoSuffix AL) (RTEMP it) (RTEMP it) (IMM 4),
                       src = [it], dst = [it], jump = []}
      topos = IOPER {assem = CBS_ (ADD NoSuffix AL) (RTEMP it) (RTEMP it) op,
                       src = [it, pt], dst = [it], jump = []}
  return (ii ++ pi ++ [m0, m1, bl, skiplen, topos], it)

munchExp (CALL (NAME "#neg") [(CONSTI i)]) = do
  t <- newTemp
  let ldr = IMOV { assem = S_ (LDR W AL) (RTEMP t) (NUM (-i)),
                   src = [], dst = [t]}
  return ([ldr], t)

munchExp (CALL (NAME "#neg") [e]) = do
  (i, t) <- munchExp e
  let rsbs = IOPER { assem = CBS_ (RSB S AL) (RTEMP t) (RTEMP t) (IMM 0),
                     src = [t], dst = [t], jump = []}
      check = IOPER {assem = BRANCH_ (BL VS) (L_ "p_throw_overflow_error"),
                     src = [], dst = [], jump =["p_throw_overflow_error"] }
  return (i ++ [rsbs, check] , t)

munchExp (CALL (NAME "#!") [e]) = do
  (i, t) <- munchExp e
  return (i ++ [IOPER {assem = CBS_ (EOR NoSuffix AL) (RTEMP t) (RTEMP t)(IMM 1),
                       src = [t], dst = [t], jump = []}], t)

munchExp (CALL (NAME "#len") [e]) = do
  (i, t) <- munchExp e
  return (i ++ [IMOV {assem = S_ (LDR W AL) (RTEMP t) (Imm (RTEMP t) 0),
                       src = [t], dst = [t]}], t)

munchExp (CALL (NAME "#skip") _) = return ([], dummy)

munchExp (CALL (NAME "#p_print_ln") es) = do
  ls <- mapM (liftM fst.munchExp) es
  let ln = IOPER {assem = BRANCH_ (BL AL) (L_ "p_print_ln"),
                  src = [], dst = [], jump = ["p_print_ln"]}
  return ((concat ls)++[ln], dummy)

munchExp (CALL (NAME "#p_read_int") [MEM e]) = do
  (i, t) <- munchExp e
  let mv = move_to_r t 0
      putchar = ljump_to_label "p_read_int"
  return (i ++ [mv, putchar], dummy)

munchExp (CALL (NAME "#p_read_char") [MEM e]) = do
  (i, t) <- munchExp e
  let mv = move_to_r t 0
      putchar = ljump_to_label "p_read_int"
  return (i ++ [mv, putchar], dummy)

munchExp (CALL (NAME "#p_putchar") [e]) = do
  (i, t) <- munchExp e
  let mv = move_to_r t 0
      putchar = ljump_to_label "putchar"
  return (i ++ [mv, putchar], dummy)

munchExp (CALL (NAME "exit") [e]) = do
  let exit = ljump_to_label "exit"
  case e of
    CONSTI n ->
      return ([ IMOV { assem = MC_ (ARM.MOV AL) R0 (IMM n),
                      src = [],
                      dst = [0] },
                exit ], dummy)
    TEMP t ->
      return ([ IMOV { assem = MC_ (ARM.MOV AL) R0 (R (RTEMP t)),
                       src = [t],
                       dst = [0] },
                exit ], dummy)
    otherwise -> do
      mv <- munchStm (IR.MOV (TEMP 0) e)
      return (mv ++ [exit], dummy)

munchExp (CALL (NAME n) [e])
  | "#p_" `isPrefixOf` n = do
    (i, t) <- munchExp e
    return  (i++ [(move_to_r t 0), (ljump_to_label (drop 1 n))], dummy)

munchExp (CALL (NAME n) e)
  | "#fst" `isPrefixOf` n = accessPair True n e
  | "#snd" `isPrefixOf` n = accessPair False n e
  | "#newpair " `isPrefixOf` n = createPair fst snd e
    where
      ls = words n
      fst = (ls !! 1)
      snd = (ls !! 2)

{- r0 / r1 : result in r0 -}
munchExp (BINEXP DIV e1 e2) = do
  (i1, t1) <- munchExp e1 -- dividend
  (i2, t2) <- munchExp e2 --divisor
  let divLabel = "__aeabi_idiv"
      moveDividend = move_to_r t1 0
      moveDivisor = move_to_r t2 1
      check = IMOV {assem = BRANCH_ (BL AL) (L_ "p_check_divide_by_zero"),
                    src = [0, 1], dst = []}
      divInstr = IMOV {assem = BRANCH_ (BL AL) (L_ divLabel),
                      src = [0, 1], dst = [0]} in
      return $ (i1 ++ i2 ++ [moveDividend, moveDivisor, check, divInstr], 0)

{- r0 % r1 : result in r1 -}
munchExp (BINEXP MOD e1 e2) = do
  (i1, t1) <- munchExp e1 -- dividend
  (i2, t2) <- munchExp e2  --divisor
  let modLabel = "__aeabi_idivmod"
      moveDividend = move_to_r t1 0
      moveDivisor = move_to_r t2 1
      check = IMOV {assem = BRANCH_ (BL AL) (L_ "p_check_divide_by_zero"),
                    src = [0, 1], dst = []}
      modInstr = IMOV {assem = BRANCH_ (BL AL) (L_ modLabel),
                  src = [0, 1], dst = [1]} in
      return $ (i1 ++ i2 ++ [moveDividend, moveDivisor, check ,modInstr], 1)

{-If munched stm is of length 2 here then it must be a SEQ conaing a naive stm and a label -}
munchExp (ESEQ (SEQ cjump@(CJUMP rop _ _ _ _) (SEQ false true)) e) = do
  cinstr <- munchStm cjump
  state <- get
  falseinstr <- munchStm false
  if (length falseinstr == 2) then
    do
    put state
    let (fCommand, fBranch) = deSeq false
    condf <- condStm fCommand
    branchf <- munchStm fBranch
    state2 <- get
    trueinstr <- munchStm true
    if(length trueinstr == 2) then
      do
      put state2
      condt <- condStm (snd $ deSeq true) -- branch info not needed
      (i, t) <- munchExp e
      return ((condf (invert rop)) ++ (condt $ same rop) ++ i, t)
    else
      do
      (i, t) <- munchExp e
      return ((condf (invert rop)) ++ branchf ++ trueinstr ++ i, t)
  else
    do
    trueinstr <- munchStm true
    (i, t) <- munchExp e
    return (cinstr ++ falseinstr ++ trueinstr ++ i, t)

munchExp (ESEQ stm e) = do
  ls <- munchStm stm
  (i, t) <- munchExp e
  return (ls++i, t)

-- TODO: add function type information
-- push all the parameters to the stack
munchExp (CALL (NAME f) es) = do
  pushParams <- mapM munchStm (concat (map pushParam es))
  return (concat pushParams ++ [bToFunc] ++ adjustSP, 0)
  where pushParam exp =
          [IR.MOV (TEMP Frame.sp) (BINEXP MINUS (TEMP Frame.sp) (CONSTI 4)),
           IR.MOV (MEM (TEMP Frame.sp)) exp]
        adjustSP = if totalParamSize == 0 then [] else
          [IOPER { assem = CBS_ (ADD NoSuffix AL) SP SP (IMM totalParamSize),
                  src = [Frame.sp],
                  dst = [Frame.sp],
                  jump = [] }]
        bToFunc =
          IOPER { assem = BRANCH_ (B AL) (L_ f),
                  src = [],
                  dst = [],
                  jump = [f] }
        totalParamSize = (length es) * 4


munchExp (CALL f es) = do
  (fi, ft) <- munchExp f -- assume result returned in ft
  ls <- mapM (liftM fst.munchExp) es
  let returnVal = move_to_r ft 0
  return ((concat ls) ++ fi ++ [returnVal], 0) -- returned in reg 0

-- NO CALLER / CALLEE SAVE CONVENTION YET !!

munchExp (TEMP t) = return ([],t)

munchExp (BINEXP MUL e1 e2) = do -- only the lower one is used
  (i1, t1) <- munchExp e1
  (i2, t2) <- munchExp e2
  tLo <- newTemp
  tHi <- newTemp
  let smull = IMOV {assem = C2_ (SMULL NoSuffix AL) (RTEMP tLo)
                    (RTEMP tHi) (RTEMP t1) (RTEMP t2),
                    src = [t1, t2], dst = [tLo, tHi]}
      cmp = IOPER {assem = MC_ (CMP AL) (RTEMP tHi) (ASR_ (RTEMP tLo) 31),
                   src = [tHi, tLo], dst = [], jump = []}
      throw = IOPER {assem = BRANCH_ (BL ARM.NE) (L_ "p_throw_overflow_error"),
                   src = [], dst = [], jump = ["p_throw_overflow_error"]}
  return $ (i1 ++ i2 ++ [smull, cmp, throw], tLo)

-- our stack implementation is different ???
-- UNCOMMENT AFTER SP handled
-- munchExp (BINEXP MINUS (TEMP 13) (CONSTI i)) = do
--   return ([IOPER {assem = CBS_ (SUB NoSuffix AL) (SP) (SP) (IMM i), src = [13], dst = [13],
--                  jump = []}], 13)
--
-- munchExp (BINEXP PLUS (TEMP 13) (CONSTI i)) = do
--   return ([IOPER {assem = CBS_ (ADD NoSuffix AL) (SP) (SP) (IMM i), src = [13], dst = [13],
--                  jump = []}], 13)

munchExp x = do
  c <- condExp x
  return $ c AL

lslOP :: Exp -> Exp -> BOp -> Int -> State TranslateState (Cond -> ([ASSEM.Instr], Temp))
lslOP e1 e2 bop int = do
  (i1, t1) <- munchExp e1
  (i2, t2) <- munchExp e2
  return $ \c -> (i1 ++ i2 ++ [IOPER {assem = CBS_ (addsubtoCalc bop $ c) (RTEMP t1) (RTEMP t1)
                  (LSL_ (RTEMP t2) (log2 int)), dst = [t1], src = [t2], jump = []}] , t1)

canlsl bop int = (bop == MINUS || bop == PLUS) && (int == 2 || int == 4 || int == 8)

condExp :: Exp -> State TranslateState (Cond -> ([ASSEM.Instr], Temp))
-- LSL inside ADD SUB  ** ugly pattern match to avoid run time loop --
condExp (BINEXP bop (BINEXP MUL e1 (CONSTI int)) e2)
  | canlsl bop int
      = lslOP e1 e2 bop int

condExp (BINEXP bop e1 (BINEXP MUL (CONSTI int) e2))
  | canlsl bop int
      = lslOP e1 e2 bop int

condExp (BINEXP bop e1 (BINEXP MUL e2 (CONSTI int)))
  | canlsl bop int
      = lslOP e1 e2 bop int

condExp (BINEXP bop (BINEXP MUL (CONSTI int) e1) e2)
  | canlsl bop int
      = lslOP e1 e2 bop int

condExp (BINEXP bop e1@(CONSTI int1) e2@(CONSTI int2))
  | bop /= PLUS && bop /= MINUS = do
    (i1, t1) <- munchExp e1
    let {cbs = bopToCBS bop}
    case cbs of
      Nothing -> fail ""
      otherwise -> return $ \c -> (i1 ++ [IOPER {assem = CBS_ ((fromJust cbs) NoSuffix c)
                                  (RTEMP t1) (RTEMP t1) (IMM int2),
                                  dst = [t1], src = [t1], jump = []}], t1)
  | otherwise = do
    (i1, t1) <- munchExp e1
    (i2, t2) <- munchExp e2
    let subs = IOPER {assem = CBS_ ((if bop == PLUS then ADD else SUB) S AL)
                      (RTEMP t1) (RTEMP t1) (R (RTEMP t2)),src = [t1, t2],
                       dst = [t1], jump = []}
        br = IOPER {assem = BRANCH_ (BL VS) (L_ "p_throw_overflow_error"),
                      src = [], dst = [], jump = ["p_throw_overflow_error"]}
    return $ \c -> (i1++i2++[subs, br], t1)

condExp (BINEXP bop (CONSTI int) e) = condExp (BINEXP bop e (CONSTI int))

condExp (BINEXP bop e (CONSTI int)) = do
  (i1, t1) <- munchExp e
  let {cbs = bopToCBS bop}
  case cbs of
    Nothing -> fail ""
    otherwise -> return $ \c -> (i1 ++ [IOPER {assem = CBS_ ((fromJust cbs) NoSuffix c)
                                (RTEMP t1) (RTEMP t1) (IMM int),
                                dst = [t1], src = [t1], jump = []}], t1)

-- Now cannot match irpre
condExp (BINEXP MINUS e1 e2) = do
  (i1, t1) <- munchExp e1
  (i2, t2) <- munchExp e2
  let subs = IOPER {assem = CBS_ (SUB S AL) (RTEMP t1) (RTEMP t1) (R (RTEMP t2)),
                    src = [t1, t2], dst = [t1], jump = []}
      br = IOPER {assem = BRANCH_ (BL VS) (L_ "p_throw_overflow_error"),
                    src = [], dst = [], jump = ["p_throw_overflow_error"]}
  return $ \c -> (i1++i2++[subs, br], t1)

  -- Now cannot match irpre
condExp (BINEXP PLUS e1 e2) = do
  (i1, t1) <- munchExp e1
  (i2, t2) <- munchExp e2
  let subs = IOPER {assem = CBS_ (ADD S AL) (RTEMP t1) (RTEMP t1) (R (RTEMP t2)),
                    src = [t1, t2], dst = [t1], jump = []}
      br = IOPER {assem = BRANCH_ (BL VS) (L_ "p_throw_overflow_error"),
                    src = [], dst = [], jump = ["p_throw_overflow_error"]}
  return $ \c -> (i1++i2++[subs, br], t1)

condExp (BINEXP bop e1 e2) = do
  (i1, t1) <- munchExp e1
  (i2, t2) <- munchExp e2
  let {cbs = bopToCBS bop}
  case cbs of
    Nothing -> fail ""
    otherwise -> return $ \c -> (i1 ++ i2 ++ [IOPER {assem = CBS_ ((fromJust cbs) NoSuffix c)
                                (RTEMP t1) (RTEMP t1) (R $ RTEMP t2),
                                dst = [t1], src = [t1, t2], jump = []}], t1)

condExp (CONSTI int) = do
  t <- newTemp
  return $ \c -> ([IMOV {assem = S_ (LDR W c) (RTEMP t) (NUM int) , dst = [t], src = []}], t)

condExp (CONSTC chr) = do
  t <- newTemp
  return $ \c -> ([IMOV {assem = MC_ (ARM.MOV c) (RTEMP t) (CHR chr), dst = [t], src = []}], t)

condExp (NAME l) = do
  t <- newTemp
  return $ \c -> ([IMOV {assem = S_ (LDR W c) (RTEMP t) (MSG l) , dst = [t], src = []}], t)

condExp (MEM (CONSTI i)) = do
  newt <- newTemp
  return $ \c -> ([IMOV {assem = S_ (ARM.LDR W c) (RTEMP newt) (NUM i) , dst = [], src = [newt]}], newt)

condExp (MEM m) = do
  (i, t) <- munchExp m
  newt <- newTemp
  return $ \c -> (i ++ [IMOV {assem = S_ (ARM.LDR W c) (RTEMP newt) (Imm (RTEMP t) 0)
                        , dst = [t], src = [newt]}], newt)

addsubtoCalc :: BOp -> (Cond -> Calc)
addsubtoCalc PLUS = (\c -> ARM.ADD NoSuffix c)
addsubtoCalc MINUS = (\c -> ARM.SUB NoSuffix c)

log2 :: Int -> Int
log2 2 = 1
log2 4 = 2
log2 8 = 3

munchMem :: Exp -> State TranslateState ([ASSEM.Instr], [Int], SLOP2)
--- PRE-INDEX ---
-- HANDLED USING optimise

-- TODO: more simplification allowed here : eval the expression if possible to a int....
---- IMMEDIATE ----
munchMem (TEMP t) = return ([], [t], Imm (RTEMP t) 0)
munchMem (BINEXP PLUS (TEMP t) (CONSTI int)) = return ([], [t], Imm (RTEMP t) int)
munchMem (BINEXP PLUS (CONSTI int) (TEMP t)) = return ([], [t], Imm (RTEMP t) int)
munchMem (BINEXP MINUS (TEMP t) (CONSTI int)) = return ([], [t], Imm (RTEMP t) (-int))
munchMem (CONSTI int) = return ([], [], NUM int)

--- ALL OTHER CASES ---
{- Including msg -}
munchMem e = do
  (i, t) <- munchExp e
  return (i, [t], MSG "SLOP2 NOT USED")

--- CAUTION : NEED TO TEST THE IMM OFFSET RANGE OF THE TARGET MACHINE ---
optimise :: [ASSEM.Instr] -> [ASSEM.Instr]
optimise (IOPER {assem = CBS_ a@(ADD NoSuffix AL) SP SP (IMM 0)} : remain) = optimise remain
optimise (IOPER { assem = CBS_ a@(ADD NoSuffix AL) (RTEMP t1) SP (IMM i)} : -- remoge this after unified
          IMOV { assem = S_ op (RTEMP t3) (Imm (RTEMP t4) i')}:remain)
  | t4 == t1 = (IMOV { assem = S_ op (RTEMP t3) (Imm SP (i+i')), src = [13], dst = [t3]}):(optimise remain)
optimise (IMOV { assem = CBS_ a@(ADD NoSuffix AL) (RTEMP t1) SP (IMM i)} :
          IMOV { assem = S_ op (RTEMP t3) (Imm (RTEMP t4) i')}:remain)
  | t4 == t1 = (IMOV { assem = S_ op (RTEMP t3) (Imm SP (i+i')), src = [13], dst = [t3]}):(optimise remain)

-- PRE-INDEX --
optimise ((IOPER { assem = (CBS_ c (RTEMP t11) (RTEMP t12) (IMM int))}) :
          (IMOV { assem = (S_ sl (RTEMP t21) (Imm (RTEMP t22) 0))}) :remain)
  | (stackEqualCond c sl) && t11 == t12 && t22 == t11
        = IMOV { assem = (S_ sl (RTEMP t21) (PRE (RTEMP t11) (opVal c * int))),src = [t11], dst = [t12]}
                : optimise remain
optimise ((IMOV { assem = MC_ (ARM.MOV _) a (R b)}):remain)
  | a == b = optimise remain
-- optimise lables but it is dangerous ..
optimise ((IOPER { assem = (BRANCH_ (B AL) (L_ a))}) : (ILABEL {assem = (LAB b)}) : remain)
  | a == b = optimise remain
optimise (x:xs) = x : (optimise xs)
optimise [] = []

stackEqualCond :: Calc -> SL -> Bool
stackEqualCond (ARM.ADD _ c1) (LDR _ c2) = c1 == c2
stackEqualCond (ARM.ADD _ c1) (STR _ c2) = c1 == c2
stackEqualCond (ARM.SUB _ c1) (LDR _ c2) = c1 == c2
stackEqualCond (ARM.SUB _ c1) (STR _ c2) = c1 == c2
stackEqualCond _ _ = False

opVal :: Calc -> Int
opVal (ARM.ADD _ _) = 1
opVal _ = -1

munchStm :: Stm -> State TranslateState [ASSEM.Instr] -- everything with out condition
munchStm (EXP call@(CALL _ _)) = do
  (intrs, reg) <- munchExp call
  return intrs

munchStm (LABEL label) = return [ILABEL {assem = LAB label, lab = label}]

-- moving stack pointer don't need to check overflow
munchStm (IR.MOV (TEMP 13) (BINEXP bop (TEMP 13) (CONSTI offset))) = do
  let op = if bop == MINUS then SUB else ADD
  return [IOPER { assem = CBS_ (op NoSuffix AL) SP SP (IMM offset),
                  src = [Frame.sp],
                  dst = [Frame.sp],
                  jump = [] } ]

munchStm (SEQ s1 s2) = do
  l1 <- munchStm s1
  l2 <- munchStm s2
  return $ l1 ++ l2

munchStm (CJUMP rop e1 (CONSTI i) t f) = do -- ASSUME CANONICAL
  (i1, t1) <- munchExp e1
  let compare = IOPER {assem = MC_ (ARM.CMP AL) (RTEMP t1) (IMM i), dst = [], src = [t1], jump = []}
      jtrue = IOPER {assem = BRANCH_ (ARM.B (same rop)) (L_ t), dst = [], src = [], jump = [t]}
  return $ i1 ++ [compare, jtrue] -- NO JFALSE AS FALSE BRANCH FOLLOWS THIS DIRECTLY

munchStm (CJUMP rop e1 e2 t f) = do -- ASSUME CANONICAL
  (i1, t1) <- munchExp e1
  (i2, t2) <- munchExp e2
  let compare = IOPER {assem = MC_ (ARM.CMP AL) (RTEMP t1) (R (RTEMP t2)), dst = [], src = [t1, t2], jump = []}
      jtrue = IOPER {assem = BRANCH_ (ARM.B (same rop)) (L_ t), dst = [], src = [], jump = [t]}
  return $ i1 ++ i2 ++ [compare, jtrue] -- NO JFALSE AS FALSE BRANCH FOLLOWS THIS DIRECTLY

munchStm (EXP e) = do
  (i, t) <- munchExp e
  return i

munchStm x = do
  m <- condStm x
  return $ m AL

-- ALLOW the suffix + cond of a load / store to change
suffixStm :: Stm -> State TranslateState (Cond -> SLType -> [ASSEM.Instr])
suffixStm (IR.MOV (MEM me) e) = do -- STR
  (i, t) <- munchExp e
  (l, ts, op) <- munchMem me
  if null l then
    return (\c -> (\suff -> i ++ [IMOV { assem = S_ (ARM.STR suff c) (RTEMP t) op, src = ts, dst = [t]}]))
  else
    let s = head ts in
    return (\c -> (\suff -> i ++ l ++ [IMOV { assem = S_ (ARM.STR suff c) (RTEMP t) (Imm (RTEMP s) 0), src = [s], dst = [t]}]))

suffixStm (IR.MOV e (MEM me)) = do -- LDR
  (i, t) <- munchExp e
  (l, ts, op) <- munchMem me
  if null l then
    return (\c -> ( \suff -> i ++ [IMOV { assem = S_ (ARM.LDR suff c) (RTEMP t) op, src = [t], dst = ts}]))
  else
    let s = head ts in
    return (\c -> (\suff -> i ++ l ++ [IMOV { assem = S_ (ARM.LDR suff c) (RTEMP t) (Imm (RTEMP s) 0), src = [s], dst = [t]}]))

condStm :: Stm -> State TranslateState (Cond -> [ASSEM.Instr])  --allow for conditions to change

condStm ir@(IR.MOV e (MEM me)) = do
  ret <- suffixStm ir
  return (\c -> ret c W)

condStm ir@(IR.MOV (MEM me) (CONSTC chr)) = do  -- remove this case if align
  ret <- suffixStm ir
  return (\c -> ret c B_)

condStm ir@(IR.MOV (MEM me) e) = do
  ret <- suffixStm ir
  return (\c -> ret c W)

condStm (IR.MOV e (CONSTI int)) = do
  (i, t) <- munchExp e
  return (\c -> i ++ [IMOV { assem = MC_ (ARM.MOV c) (RTEMP t) (IMM int), src = [], dst = [t]}])

condStm (IR.MOV e1 e2) = do  --In which sequence ?
  (i1, t1) <- munchExp e1
  (i2, t2) <- munchExp e2
  return (\c -> i1 ++ i2 ++ [move_to_r t2 t1])

condStm (IR.PUSH e) = do
  (i, t) <- munchExp e
  return (\c -> i ++ [IMOV {assem = STACK_ (ARM.PUSH c) [RTEMP t], dst = [t], src = []}]) --sp here or not ??

condStm (IR.POP e) = do
  (i, t) <- munchExp e
  return (\c -> i ++ [IMOV {assem = STACK_ (ARM.POP c) [RTEMP t], dst = [t], src = []}])

condStm (JUMP e ls) = do
  case e of
    (CONSTI 1) ->
      return (\c -> [IOPER { assem = BRANCH_ (ARM.B AL) (L_ (head ls)),
                            dst = [],
                            src = [],
                            jump = [head ls] }])
    (CONSTI 0) -> return (\c -> [])
    otherwise -> do
      (i, t) <- munchExp e
      return (\c -> [IOPER { assem = MC_ (CMP c) (RTEMP t) (IMM 1),
                             dst = [],
                             src = [],
                             jump = [] },
                     IOPER { assem = BRANCH_ (ARM.B c) (L_ (head ls)),
                             dst = [],
                             src = [],
                             jump = [] }])

condStm (NOP) = return $ \c -> []

condStm t = fail $ show t

munchBuiltInFuncFrag :: Fragment -> State TranslateState [ASSEM.Instr]
munchBuiltInFuncFrag (PROC stm frame) = do
  munch <- munchStm stm
  return (pushlr : munch ++ [poppc])

munchDataFrag :: Fragment -> [ASSEM.Instr]
munchDataFrag (STRING label str)
  = [ILABEL {assem = (M label (length str) str), lab = label}]

createPair :: String -> String -> [Exp] -> State TranslateState ([ASSEM.Instr], Temp)
-- pre : exps contains only two param
createPair s1 s2 exps = do
  (i1, t1) <- munchExp (exps !! 0)
  (i2, t2) <- munchExp (exps !! 1)
  tadddr <- newTemp -- pair addr
  let
      ld8 = IMOV { assem = (S_ (LDR W AL) R0 (NUM 8)), src = [], dst = [0]}
      ld4 = IMOV { assem = (S_ (LDR W AL) R0 (NUM 4)), src = [], dst = [0]}
      malloc = IOPER { assem = BRANCH_ (BL AL) (L_ "malloc"), src = [0], dst = [0], jump = ["malloc"]}
      strPairAddr = IMOV { assem = MC_ (ARM.MOV AL) (RTEMP tadddr) (R R0), src = [0], dst = [tadddr]}
      savefst = IMOV { assem = (S_ (STR W {- suffix1 -} AL) (RTEMP t1) (Imm R0 0)), src = [t1, 0], dst = []}
      savesnd = IMOV { assem = (S_ (STR W {- suffix2 -} AL) (RTEMP t2) (Imm R0 0)), src = [t2, 0], dst = []}
      strfstaddr = IMOV { assem = (S_ (STR W AL) R0 (Imm (RTEMP tadddr) 0)), src = [tadddr, 0], dst = []}
      strsndaddr = IMOV { assem = (S_ (STR W AL) R0 (Imm (RTEMP tadddr) 4)), src = [tadddr, 0], dst = []}
      strpaironstack= IMOV { assem = (S_ (STR W AL) (RTEMP tadddr) (Imm (RTEMP 13) 0)), src = [t1, 13], dst = [0]}
  return ([ld8, malloc, strPairAddr] ++ i1 ++ [ld4, malloc, savefst, strfstaddr]
           ++ i2 ++ [ld4, malloc, savesnd, strsndaddr, strpaironstack], dummy)

accessPair :: Bool -> String -> [Exp] -> State TranslateState ([ASSEM.Instr], Temp)
accessPair isfst typestr [e] = do
  (i, t) <- munchExp e
  let offset = if isfst then 0 else 4
      getpaddr = move_to_r t 0
      check = IOPER { assem = BRANCH_ (BL AL) (L_ "p_check_null_pointer")
                      , src = [0], dst = [], jump = ["p_check_null_pointer"]}
      s1 = IMOV {assem = (S_ (LDR {-(if one then SB else W)-} W AL) (RTEMP t) (Imm (RTEMP t) offset)), src = [t], dst = [t]}
  return (i ++ [getpaddr, check, s1], t)  -- cannot handle sb/w here as only return reg


-------------------- Utilities ---------------------
condIR = [IR.EQ, IR.LT, IR.LE, IR.GT, IR.GE, IR.NE]
condARM = [ARM.EQ, ARM.LT, ARM.LE, ARM.GT, ARM.GE, ARM.NE]

invert :: ROp -> Cond
invert a = fromJust $ lookup a (zip condIR (reverse condARM))

same :: ROp -> Cond
same a = fromJust $ lookup a (zip condIR condARM)

deSeq :: Stm -> (Stm, Stm)
deSeq (SEQ s1 s2) = (s1, s2)

showStm stm = do
  putStrLn ""
  munch <- evalState (optimsedMunch stm) Translate.newTranslateState
  putStrLn ""
  return $ ()

showExp exp = do
  munch <- evalState (munchExp exp) Translate.newTranslateState
  return (munch)

munch file = do
  putStrLn ""
  ast <- parseFile file
  ast' <- analyzeAST ast
  let (stm, s) = runState (Translate.translate ast') Translate.newTranslateState
      (builtInFrags, s') = runState (genProcFrags (Set.toList $ builtInSet s)) s -- generate builtIn
      userFrags = map (\(Frame.PROC stm _) -> stm) (Translate.procFrags s)
      dataFrags = map munchDataFrag ( Translate.dataFrags s' )
      canonState = CanonState { C.tempAlloc = Translate.tempAlloc s',
                                C.controlLabelAlloc = Translate.controlLabelAlloc s'}
      (stm', s'') = runState (transform stm) canonState
      transState = s' { Translate.tempAlloc = C.tempAlloc s'',
                        Translate.controlLabelAlloc = C.controlLabelAlloc s'' }
      (userFrags', s''') = runState (munchmany userFrags) transState -- munch functions
      arms = evalState (munchmany stm') s'''
      substitute = optimise (normAssem [(13, SP), (14, LR), (15, PC), (1, R1), (0, R0)] arms)
      out = filter (\x -> not $ containsDummy x) substitute
      substitute' = optimise (normAssem [(13, SP), (14, LR), (15, PC), (1, R1), (0, R0)] userFrags')
      out' = filter (\x -> not $ containsDummy x) substitute'
      totalOut = intercalate ["\n"] (map (map show) builtInFrags) ++ ["\n"] ++
                 concat (map (lines . show) (concat dataFrags)) ++ ["\n"] ++
                 (map show (out' ++ out))
  mapM putStrLn $ zipWith (++) (map (\x -> (show x) ++"  ") [0..]) totalOut
  putStrLn ""
  return ()

  where genProcFrags :: [Int] -> State TranslateState [[ASSEM.Instr]]
        genProcFrags ids = do
          let gens = map (\n -> genBuiltIns !! n) ids
          pfrags <- foldM (\acc f -> f >>= \pfrag -> return $ acc ++ [pfrag]) [] gens
          return pfrags

munchmany [] = return []
munchmany (x:xs) = do
  m <- munchStm x
  ms <- munchmany xs
  return $ (m++ms)

optimsedMunch stm = do
  m <- munchStm stm
  let substitute = optimise (normAssem [(13, SP), (14, LR), (15, PC), (1, R1), (0, R0)] m)
      out = filter (\x -> not $ containsDummy x) substitute
  return $ mapM putStrLn $ zipWith (++) (map (\x -> (show x) ++"  ") [0..]) (map show out)

call = CALL (CONSTI 1) [(CONSTI 7)]
-- pre-Index sample --
assemPre = (IOPER { assem = (CBS_ (ARM.ADD NoSuffix ARM.EQ) (RTEMP 1) (RTEMP 1) (IMM 2)), src = [1], dst = [1], jump = []}) :
           (IMOV { assem = (S_ (ARM.LDR W ARM.EQ) (RTEMP 2) (Imm (RTEMP 1) 0)), src = [2], dst = [1]}) : []
irPre = IR.MOV (BINEXP MINUS (TEMP 2) (CONSTI 1)) (MEM (TEMP 2))

type GenBuiltIn = State TranslateState [ASSEM.Instr]

genBuiltIns = [p_print_ln,
               p_print_int,
               p_print_bool,
               p_print_string,
               p_print_reference,
               p_check_null_pointer,
               p_throw_runtime_error,
               p_read_int,
               p_read_char,
               p_free_pair,
               p_check_array_bounds,
               p_throw_overflow_error]


p_print_ln :: GenBuiltIn
p_print_ln = do
  msg <- newDataLabel
  addFragment (Frame.STRING msg "\0")
  return $[add_label "p_print_ln",
           pushlr,
           ld_msg_toR0 msg,
           r0_add4,
           ljump_to_label "puts",
           r0_clear,
           ljump_to_label "fflush",
           poppc]

p_print_int :: GenBuiltIn
{-In ref compiler this temp is R1 -}
p_print_int = do
 msg <- newDataLabel
 temp <- newTemp
 addFragment (Frame.STRING msg "%d\0")
 return $[add_label "p_print_int",
          pushlr,
          move_to_r 0 temp,
          IMOV { assem = S_ (LDR W AL) (RTEMP temp) (MSG msg), src = [], dst = [temp]}]
          ++ end

p_print_bool :: GenBuiltIn
p_print_bool = do
  truemsg <- newDataLabel
  falsemsg <- newDataLabel
  addFragment (Frame.STRING truemsg "true\0")
  addFragment (Frame.STRING falsemsg "false\0")
  return $[add_label "p_print_bool",
          pushlr,
          cmp_r0,
          ld_cond_msg_toR0 truemsg ARM.NE,
          ld_cond_msg_toR0 falsemsg ARM.EQ]
          ++ end


p_print_string :: GenBuiltIn
p_print_string = do
  msg <- newDataLabel
  addFragment (Frame.STRING msg "%.*s\0")
  return $[add_label "p_print_string",
          pushlr,
          IMOV {assem = S_ (LDR W AL) R1 (Imm R0 0), src = [0], dst = [1]},
          IOPER { assem = CBS_ (ADD NoSuffix AL) R2 R0 (IMM 4), src = [0], dst = [2], jump = []},
          ld_msg_toR0 msg] ++ end

p_print_reference :: GenBuiltIn
p_print_reference = do
  msg <- newDataLabel
  addFragment (Frame.STRING msg "%p\0")
  return $[add_label "p_print_reference",
          pushlr,
          move_to_r 0 1,
          ld_msg_toR0 msg] ++ end

p_check_null_pointer :: GenBuiltIn
p_check_null_pointer = do
  msg <- newDataLabel
  addFragment (Frame.STRING msg "NullReferenceError: dereference a null reference\n\0")
  let s = "p_throw_runtime_error"
  return $[add_label "p_check_null_pointer",
          pushlr,
          cmp_r0,
          ld_cond_msg_toR0 msg ARM.EQ,
          ljump_cond s ARM.EQ,
          poppc]

p_throw_runtime_error :: GenBuiltIn
p_throw_runtime_error = do
  let s = "p_print_string"
  return [add_label "p_throw_runtime_error",
          jump_to_label s,
          IMOV {assem = MC_ (ARM.MOV AL) R0 (IMM (-1)), src = [], dst = [0]},
          jump_to_label "exit"]

p_read_int :: GenBuiltIn
p_read_int = do
  r <- p_read "%d\0"
  return $ (add_label "p_read_int"): r

p_read_char :: GenBuiltIn
p_read_char = do
  r <- p_read " %c\0"
  return $ (add_label "p_read_char"): r

p_read :: String -> GenBuiltIn
p_read str =  do
  msg <- newDataLabel
  addFragment (Frame.STRING msg str)
  return [pushlr,
          move_to_r 0 1,
          ld_msg_toR0 msg,
          r0_add4,
          ljump_to_label "scanf",
          poppc]

p_free_pair :: GenBuiltIn
p_free_pair = do
  msg <- newDataLabel
  let str = "NullReferenceError: dereference a null reference\n\0"
      runTimeError = "p_throw_runtime_error"
  addFragment (Frame.STRING msg str)
  return [add_label "p_free_pair",
          pushlr,
          cmp_r0,
          ld_cond_msg_toR0 msg ARM.EQ,
          ljump_cond runTimeError ARM.EQ,
          IOPER { assem = STACK_ (ARM.PUSH AL) [R0], src = [0], dst = [Frame.fp], jump = []},
          IMOV {assem = S_ (LDR W AL) R0 (Imm R0 0), src = [0], dst = [0]},
          ljump_to_label "free",
          IMOV {assem = S_ (LDR W AL) R0 (Imm (RTEMP Frame.fp) 0), src = [Frame.fp], dst = [0]},
          IMOV {assem = S_ (LDR W AL) R0 (Imm R0 4), src = [0], dst = [0]},
          ljump_to_label "free",
          IOPER { assem = STACK_ (ARM.POP AL) [R0], src = [Frame.fp], dst = [Frame.fp, 0], jump = []},
          ljump_to_label "free",
          poppc]

{-How to handle array access in translate && munch? -}
p_check_array_bounds :: GenBuiltIn
p_check_array_bounds = do
  msgneg <- newDataLabel
  msgover <- newDataLabel
  t <- newTemp -- r1
  addFragment (Frame.STRING msgneg "ArrayIndexOutOfBoundsError: negative index\n\0")
  addFragment (Frame.STRING msgover "ArrayIndexOutOfBoundsError: index too large\n\0")
  return [add_label "p_check_array_bounds",
          pushlr,
          cmp_r0,
          ld_cond_msg_toR0 msgneg ARM.LT,
          ljump_cond "p_throw_runtime_error" ARM.LT,
          IMOV {assem = S_ (LDR W AL) (RTEMP t) (Imm (RTEMP t) 0), src = [t], dst = [0]},
          cmp_r0,
          ld_cond_msg_toR0 msgover ARM.CS,
          ljump_cond "p_throw_runtime_error" ARM.CS,
          poppc]

{- where to call ? -}
p_throw_overflow_error :: GenBuiltIn
p_throw_overflow_error = do
  msg <- newDataLabel
  addFragment (Frame.STRING msg $ "OverflowError: the result is too small/large"
                                   ++ " to store in a 4-byte signed-integer.\n")
  return [add_label "p_throw_overflow_error",
          ld_msg_toR0 msg, ljump_to_label "BL p_throw_runtime_error"]

{- where to call ? -}
p_check_divide_by_zero :: GenBuiltIn
p_check_divide_by_zero = do
  msg <- newDataLabel
  addFragment (Frame.STRING msg "DivideByZeroError: divide or modulo by zero\n\0")
  return [add_label "p_check_divide_by_zero",
          pushlr,
          IOPER {assem = MC_ (CMP AL) R1 (IMM 0), src = [1], dst = [], jump = []},
          ld_cond_msg_toR0 msg ARM.EQ,
          ljump_cond "p_throw_runtime_error" ARM.EQ,
          poppc]
