module BackEnd.Assem where

import Data.List as List
import BackEnd.Temp as Temp
import qualified BackEnd.Instructions as Arm
import BackEnd.IR

{- Note
  ------------------------------------------------------------------------------
  Assem is an interface that can abtract away details of specific architecture
  to perform liveness analysis and register allocation. Munch (instruction
  selection) will wrap the selected ARM instruction in this interface.

  The design is inspired by the book Modern Compiler Implementation in ML.
-}

data Instr = IOPER  { assem :: Arm.Instr,
                      dst :: [Temp.Temp],
                      src :: [Temp.Temp],
                      jump :: [String]}
           | ILABEL { assem :: Arm.Instr,
                      lab :: Temp.Label }
           | IMOV   { assem :: Arm.Instr,
                      dst  :: [Temp.Temp],
                      src :: [Temp.Temp] }
            deriving (Eq)

-- extract all regs used in an instruction
assemReg (IOPER _ d s _) = nub $ d ++ s
assemReg (IMOV _ d s) = nub $ d ++ s
assemReg _ = []

showInstr (IOPER assem d s jump) =
    Arm.output_show assem ++ " dst : " ++ show d ++
    " src: " ++ show s ++ " jump: " ++ show jump
showInstr (IMOV assem d s) =
    Arm.output_show assem ++ " dst : " ++ show d ++
    " src: " ++ show s
showInstr (ILABEL assem l) =
    Arm.output_show assem ++ " label: " ++ show l

-- output the final assembly
showAssem :: [[Instr]] -> [[Instr]]-> [Instr] -> [String]
showAssem builtInFrags dataFrags code
  = intercalate ["\n"] (([[".data"]] ++ map (lines . show) (concat dataFrags)) ++
                        ([[".text"], ["\n"], [".global main"]] ++ [map show code]
                        ++ [[".ltorg"]]) ++ (map (map show) builtInFrags))

instance Prelude.Show Instr where
    show (IOPER assem dst src jump) = "    " ++ Arm.output_show assem
    show (ILABEL assem lab) = Arm.output_show assem
    show (IMOV assem dst src) = "    " ++ Arm.output_show assem

intToReg :: Int -> Arm.REG
intToReg 0 = Arm.R0
intToReg 1 = Arm.R1
intToReg 2 = Arm.R2
intToReg 3 = Arm.R3
intToReg 4 = Arm.R4
intToReg 5 = Arm.R5
intToReg 6 = Arm.R6
intToReg 7 = Arm.R7
intToReg 8 = Arm.R8
intToReg 9 = Arm.R9
intToReg 10 = Arm.R10
intToReg 11 = Arm.R11
intToReg 12 = Arm.R12
intToReg 13 = Arm.SP
intToReg 14 = Arm.LR
intToReg 15 = Arm.PC


-- utilities to change temporaries in instruction to machine register
normInstr :: (Arm.Instr -> Arm.Instr) -> Instr -> Instr
normInstr func (IOPER assem dst src jump) = IOPER (func assem) dst src jump
normInstr func (ILABEL assem lab) = ILABEL (func assem) lab
normInstr func (IMOV assem dst src) = IMOV (func assem) dst src

normAssem ::[(Int, Arm.REG)] -> [Instr] -> [Instr]
normAssem ((i, r):ls) instrs = normAssem ls (map (normInstr $ Arm.normInstr i r) instrs)
normAssem [] instrs = instrs

normAssem' ::[(Int, Int)] -> [Instr] -> [Instr]
normAssem' ((i, r):ls) instrs =
    normAssem' ls (map (normInstr $ Arm.normInstr i (intToReg r)) instrs)
normAssem' [] instrs = instrs


containsDummy :: Instr -> Bool
containsDummy (IOPER assem _ _ _) = Arm.dummyInstr assem
containsDummy (ILABEL assem _) = Arm.dummyInstr assem
containsDummy (IMOV assem _ _) = Arm.dummyInstr assem

updateReg :: Int -> Int -> [Int] -> [Int]
updateReg from to list = [if x == from then to else x|x <- list]

normGK :: Int -> Int -> [Instr] -> [Instr]
normGK _ _ [] = []
normGK from to ((IMOV assem dst src):remain) 
    = (IMOV assem (updateReg from to dst) (updateReg from to src)) : normGK from to remain
normGK from to ((IOPER assem dst src jump):remain) 
    = (IOPER assem (updateReg from to dst) (updateReg from to src) jump) : normGK from to remain
normGK from to (a@(ILABEL _ _):remain) = a : normGK from to remain

normAll from to instr = normGK from to $ normAssem' [(from, to)] instr