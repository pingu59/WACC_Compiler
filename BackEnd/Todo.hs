-- 1. Utility for writing assembly to files
-- 2. write a script to allow emulation and auto testing
-- 3. output could be different to the formal one
module BackEnd.Todo where

import FrontEnd.AST
import FrontEnd.SemanticAnalyzer

-- 0	.text
-- 1
-- 2	.global main
-- 3	main:
-- 4		PUSH {lr}
-- 5		LDR r4, =-1
-- 6		MOV r0, r4
-- 7		BL exit
-- 8		LDR r0, =0
-- 9		POP {pc}
-- 10		.ltorg
-- 11

indent :: String -> String
indent s = "\t\t" ++ s

nextline :: String -> String
nextline s = s ++ "\n"

writeCode :: String -> [String] -> IO()
writeCode filename assembly = do
  writeFile outputname (concat assembly)
    where outputname = (take (length filename - 5) filename) ++ ".s"

sampleExit = map nextline $ [".text", "", ".global main", "main:"] ++
              (map indent ["PUSH {lr}", "LDR r4, =-1", "MOV r0, r4", "BL exit",
              "LDR r0, =0", "POP {pc}", ".ltorg", ""])
