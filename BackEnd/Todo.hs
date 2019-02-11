-- 1. Utility for writing assembly to files
-- 2. write a script to allow emulation and auto testing
-- 3. output could be different to the formal one
module BackEnd.Todo where

import FrontEnd.AST
import FrontEnd.SemanticAnalyzer
import System.Environment

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

main = do
  args <- getArgs
  case args of
    [file] -> do
      writeCode file sampleExit
    _ -> fail ("File does not exist\n")
