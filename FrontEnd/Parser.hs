module FrontEnd.Parser where

import System.IO
import Control.Monad
import Control.Monad.Except
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language

import Text.ParserCombinators.Parsec.Pos

import FrontEnd.Lexer
import FrontEnd.AST

parseProgramF :: Parser (ProgramF ())
parseProgramF = whiteSpace >> wrapPos (do{
              reserved "begin";
              fs <- many (try parseFuncF);
              stat <- parseStatListF;
              reserved "end";
              eof;
              return $ Program fs stat})

parseFuncF :: Parser (FuncF ())
parseFuncF = whiteSpace >> wrapPos (do{
             t <- parseTypeF;
             ident <- parseIdentF;
             ps <- parens (commaSep parseParamF);
             reserved "is";
             stat <- parseStatListF;
             checkReturnExit stat;
             reserved "end";
             return $ Func t ident ps stat})
    where checkReturnExit (Ann (StatList stats) (pos, None))
            = case lastStat of
                Return _ -> return ()
                Exit _ -> return ()
                If _ stat1 stat2 ->
                      checkReturnExit stat1 >>
                      checkReturnExit stat2
                While _ stat -> checkReturnExit stat
                Subroutine stat -> checkReturnExit stat
                otherwise -> fail "Expected return or junk after return"
           where Ann lastStat _ = last stats

parseParamF :: Parser (ParamF ())
parseParamF = whiteSpace >> wrapPos (do{
              t <- parseTypeF;
              ident <- parseIdentF;
              return $ Param t ident})

parseTypeF :: Parser (TypeF ())
parseTypeF = try parseArrayTypeF
         <|> try parseBaseTypeF
         <|> parsePairTypeF

parseArrayTypeF :: Parser (TypeF ())
parseArrayTypeF = do
                  whiteSpace
                  pos <- getPosition
                  t <- (parseBaseTypeF <|> parsePairTypeF)
                  rs <- many (try $ reserved "[]")
                  return $ foldl (\acc x -> Ann (TArray acc) (pos, None)) t rs

parseBaseTypeF :: Parser (TypeF ())
parseBaseTypeF = whiteSpace >> wrapPos (do{
                 ((reserved "int" >> (return $ TInt ))
                  <|> (reserved "bool" >> (return $ TBool))
                  <|> (reserved "char" >> (return $ TChar))
                  <|> (reserved "string" >> (return $ TStr)))})

parsePairTypeF :: Parser (TypeF ())
parsePairTypeF = whiteSpace >> wrapPos (do{
                 string "pair";
                 reservedOp "(";
                 t1 <- parsePairElemTypeF;
                 comma;
                 t2 <- parsePairElemTypeF;
                 reservedOp ")";
                 return $ TPair t1 t2})
        where parsePairElemTypeF :: Parser (TypeF ())
              parsePairElemTypeF = try parseArrayTypeF
                               <|> try parseBaseTypeF
                               <|> (wrapPos(do{string "pair";return $ Any}))

parseStatListF :: Parser (StatListF ())
parseStatListF = whiteSpace >> wrapPos (do{
                  stat <- parseStatF;
                 (try (semi >>
                    parseStatListF >>= \(Ann (StatList rest) _) ->
                    return $ StatList (stat:rest))
                    <|> (return $ StatList [stat]))})

parseStatF :: Parser (StatF ())
parseStatF = whiteSpace >>
           ( parseSkipStatF
         <|> try parseDeclareStatF
         <|> try parseAssignStatF
         <|> parseReadStatF
         <|> parseFreeStatF
         <|> parseReturnStatF
         <|> parseExitStatF
         <|> parsePrintStatF
         <|> parsePrintlnStatF
         <|> parseIfStatF
         <|> parseWhileStatF
         <|> parseSubroutineStatF )

parseDeclareStatF :: Parser (StatF ())
parseDeclareStatF = wrapPos (do{
                    t <- parseTypeF;
                    ident <- parseIdentF;
                    reservedOp "=";
                    rhs <- parseAssignRHSF;
                    return $ Declare t ident rhs})

parseAssignStatF :: Parser (StatF ())
parseAssignStatF = wrapPos (do{
                   lhs <- parseAssignLHSF;
                   reservedOp "=";
                   rhs <- parseAssignRHSF;
                   return $ Assign lhs rhs})

parseReadStatF :: Parser (StatF ())
parseReadStatF = wrapPos(do {
                 reserved "read";
                 lhs <- parseAssignLHSF;
                 return $ Read lhs})

parseSkipStatF :: Parser (StatF ())
parseSkipStatF = whiteSpace >> wrapPos(do {reserved "skip"; return $ Skip})

parseFreeStatF :: Parser (StatF ())
parseFreeStatF = parseBaseStat "free"

parseReturnStatF :: Parser (StatF ())
parseReturnStatF = parseBaseStat "return"

parseExitStatF :: Parser (StatF ())
parseExitStatF = parseBaseStat "exit"

parsePrintStatF :: Parser (StatF ())
parsePrintStatF = parseBaseStat "print"

parsePrintlnStatF :: Parser (StatF ())
parsePrintlnStatF = parseBaseStat "println"

parseBaseStat :: String -> Parser (StatF ())
parseBaseStat s = whiteSpace >> wrapPos(do {
                    reserved s;
                    expr <- parseExprF;
                    return $ (baseStat s) expr})

baseStat :: String -> (ExprF a -> Stat a)
baseStat "exit" = (\s -> Exit s)
baseStat "println" = (\s -> Println s)
baseStat "free" = (\s -> Free s)
baseStat "print" = (\s -> Print s)
baseStat "return" = (\s -> Return s)
baseStat _ = fail("Cannot reach here")

parseIfStatF :: Parser (StatF ())
parseIfStatF = whiteSpace >> wrapPos(do {
               reserved "if";
               expr <- parseExprF;
               reserved "then";
               stat1 <- parseStatListF;
               reserved "else";
               stat2 <- parseStatListF;
               reserved "fi";
               return $ If expr stat1 stat2})

parseWhileStatF :: Parser (StatF ())
parseWhileStatF = whiteSpace >> wrapPos(do {
                  reserved "while";
                  expr <- parseExprF;
                  reserved "do";
                  stat <- parseStatListF;
                  reserved "done";
                  return $ While expr stat})

parseSubroutineStatF :: Parser (StatF ())
parseSubroutineStatF = whiteSpace >> wrapPos(do {
                       reserved "begin";
                       stat <- parseStatListF;
                       reserved "end";
                       return $ Subroutine stat})


parseAssignLHSF :: Parser (AssignLHSF ())
parseAssignLHSF = wrapPos (do
                  (do {elem <- try parsePairElemF; return $ PairElemLHS elem}
                   <|> do {elem <- try parseArrayElemF;return $ ArrayElemLHS elem}
                   <|> do {ident <- try parseIdentF; return $ IdentLHS ident}))

parseAssignRHSF :: Parser (AssignRHSF ())
parseAssignRHSF = (wrapPos (do {expr <- parseExprF; return $ ExprRHS expr})
             <|> parseNewPairRHSF
             <|> wrapPos (do {elem <- parsePairElemF; return $ PairElemRHS elem})
             <|> parseCallRHSF
             <|> parseArrayLiterRHSF)

parseArrayLiterRHSF :: Parser (AssignRHSF ())
parseArrayLiterRHSF = wrapPos (do{
                      whiteSpace;
                      pos <- getPosition;
                      reservedOp "[";
                      es <- commaSep parseExprF;
                      reservedOp "]";
                      return $ ArrayLiter es})

parseNewPairRHSF :: Parser (AssignRHSF ())
parseNewPairRHSF = wrapPos (do{
                  pos <- getPosition;
                  reserved "newpair";
                  reservedOp "(";
                  expr1 <- parseExprF;
                  reservedOp ",";
                  expr2 <- parseExprF;
                  reservedOp ")";
                  return $ NewPair expr1 expr2})

parseCallRHSF :: Parser (AssignRHSF ())
parseCallRHSF = wrapPos (do {reserved "call";
                            ident <- parseIdentF;
                            args <- parens (commaSep parseExprF);
                            return $ Call ident args})

parsePairElemF :: Parser (PairElemF ())
parsePairElemF = wrapPos
                 ( do {reserved "fst";
                   expr <- parseExprF;
                   return $ PairElemFst expr}
                    <|> do {reserved "snd";
                    expr <- parseExprF;
                    return $ PairElemSnd expr})


parseExprF :: Parser (ExprF ())
parseExprF = do
             whiteSpace
             expr <- buildExpressionParser table term
             checkOverFlow expr
             checkPrefix expr
             return $ expr
     where checkPrefix (Ann (UExpr uop ef@(Ann e _)) _)
            = case e of
                LiterExpr liter ->
                  if (uop == Pos || uop == Neg) && not (isIntLiter liter)
                  then fail "syntatic error"
                  else  return ()
                otherwise -> checkPrefix ef
           checkPrefix (Ann (BExpr _ e1 e2) _)
            = checkPrefix e1 >> checkPrefix e2
           checkPrefix (Ann (BracketExpr e) _) = checkPrefix e
           checkPrefix (Ann (ArrayExpr (Ann (ArrayElem _ es) _)) _)
             = mapM_ checkPrefix es
           checkPrefix _ = return ()

           isIntLiter (Ann (IntLiter _) _) = True
           isIntLiter liter = False

           checkOverFlow intexpr = if invalid intexpr then fail("Int Overflow")
            else return ()
              where
                invalid (Ann (UExpr Neg(Ann (LiterExpr(Ann (IntLiter i)_))_))_) = i > 2^31
                invalid (Ann (LiterExpr(Ann (IntLiter i)_))_) = i > 2^31 -1
                invalid _ = False


table = [ [unary symbol "+" (UExpr Pos),
           unary symbol "-" (UExpr Neg),
           unary symbol"!" (UExpr Not),
           unary reserved "len" (UExpr Len),
           unary reserved "ord" (UExpr Ord),
           unary reserved "chr" (UExpr Chr)],
          [binary "*" (BExpr Mul) AssocLeft,
           binary "/" (BExpr Div) AssocLeft,
           binary "%" (BExpr Mod) AssocLeft],
          [binary "+" (BExpr Plus) AssocLeft,
           binary "-" (BExpr Minus) AssocLeft],
          [binary ">=" (BExpr GEq) AssocLeft, --Don't mess up order between >= and >
           binary ">" (BExpr G) AssocLeft,
           binary "<=" (BExpr LEq) AssocLeft,
           binary "<" (BExpr L) AssocLeft],
          [binary "==" (BExpr Eq) AssocLeft,
           binary "!=" (BExpr NEq) AssocLeft],
          [binary "&&" (BExpr And) AssocLeft],
          [binary "||" (BExpr Or) AssocLeft]
        ]

unary operation n f =
  Prefix . chainl1 (try (whiteSpace >>
                    getPosition >>= \pos ->
                    operation n >>
                    (return $ \e -> Ann (f e) (pos, None)))) $ return (.)

binary n f assoc =
  Infix (try (whiteSpace >>
         getPosition >>= \pos ->
         symbol n >>
         (return $ (\e1 e2 -> Ann (f e1 e2) (pos, None))))) assoc

term :: Parser (ExprF ())
term =  try parseLiterExprF
   <|>  try parseArrayExprF
   <|>  try parseIdentExprF
   <|>  try parseBracketExprF


parseArrayExprF :: Parser (ExprF ())
parseArrayExprF = wrapPos(do { a <- parseArrayElemF; return $ ArrayExpr a})

parseBracketExprF :: Parser (ExprF ())
parseBracketExprF = wrapPos(do {pos <- getPosition;
                                reservedOp "(";
                                exprF <- parseExprF;
                                reservedOp ")";
                                return $ BracketExpr exprF
                                })

parseLiterExprF :: Parser (ExprF ())
parseLiterExprF = wrapPos(do {l <- parseLiterF; return $ LiterExpr l})

parseIdentExprF :: Parser (ExprF ())
parseIdentExprF = whiteSpace >> wrapPos (do {i <- parseIdentF; return $ IdentExpr i})

parseLiterF :: Parser (LiterF ())
parseLiterF = try parseIntLiterF
         <|> try parseBoolLiterF
         <|> try parseCharLiterF
         <|> try parseStringLiterF
         <|> try parsePairLiterF

parseIntLiterF :: Parser (LiterF ())
parseIntLiterF = wrapPos (do {x <- integer; return $ IntLiter x})

parseBoolLiterF :: Parser (LiterF ())
parseBoolLiterF = wrapPos (do {
                  (do {reserved "true";return $ BoolLiter True}
                      <|> (do {reserved "false"; return $ BoolLiter False}))})

parseCharLiterF :: Parser (LiterF ())
parseCharLiterF = wrapPos ((try catchWrongEscape >> fail "wrong escape")
                            <|> (do {c <- charLiteral; return $ CharLiter c}))
     where catchWrongEscape =
             do
               char '\''
               char '\"'
               char '\''
               return '\"'


parseStringLiterF :: Parser (LiterF ())
parseStringLiterF = wrapPos(do {s <- stringLiteral; return $ StringLiter s})

parsePairLiterF :: Parser (LiterF ())
parsePairLiterF = wrapPos(do {reserved "null"; return Null})

parseIdentF :: Parser (IdentF ())
parseIdentF = wrapPos (do {i <- ident; return $ Ident i})

parseArrayElemF :: Parser (ArrayElemF ())
parseArrayElemF = wrapPos(do {
                  i <- parseIdentF;
                  exprs <- many1 (try parseIndex);
                  return $ ArrayElem i exprs})
           where parseIndex :: Parser (ExprF ())
                 parseIndex = do
                              expr <- brackets parseExprF
                              return expr

wrapPos :: Parser(a) -> Parser(Ann a)
wrapPos a = do
            pos <- getPosition
            ret <- a
            return $ Ann ret (pos, None)

parseFile :: String -> IO (ProgramF ())
parseFile file =
  do
    program <- readFile file
    case parse parseProgramF "" program of
      Left e -> print e >>
                fail ("parse error: " ++ "at line " ++ line e ++ " and col " ++ col e ++ " with file " ++ file)
      Right r -> return r
      where line = \e -> show $ sourceLine $ errorPos e
            col = \e -> show $ sourceLine $ errorPos e
            name = \e -> show $ sourceName $ errorPos e
