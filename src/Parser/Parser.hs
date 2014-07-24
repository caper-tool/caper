module Parser.Parser(parseFile, parseString, parseAExpression, parseBExpression, aExpressionParser, statementParser, parseStatement) where

import Debug.Trace
import System.IO
import Control.Monad
import Control.Monad.Error
import Data.List
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token
import Parser.AST
--import Environment

languageDef =
  emptyDef { Token.commentStart    = "/*"
           , Token.commentEnd      = "*/"
           , Token.commentLine     = "//"
           , Token.identStart      = letter
           , Token.identLetter     = alphaNum
           , Token.caseSensitive   = True
           , Token.reservedNames   = [ "if"
                                     , "else"
                                     , "while"
                                     , "do"
                                     , "skip"
                                     , "true"
                                     , "false"
                                     , "not"
                                     , "and"
                                     , "or"
                                     , "return"
                                     , "function"
                                     , "fork"
                                     , "region"
                                     , "predicate"
                                     , "("
                                     , ")"
                                     , "{"
                                     , "}"
                                     , "]"
                                     , "["
                                     , "0p"
                                     , "1p"
                                     , "#cells"
                                     ]
           , Token.reservedOpNames = ["+", "-", "*", "/", ":="
                                     , "=", "!=", "<", ">", ">=", "<="
                                     , "and", "or", "not", "?", ":"
                                     , "&*&", "=p=", "=v=", "$", "!"
                                     , "==", "|->", "@"
                                     ]
           }

lexer = Token.makeTokenParser languageDef

identifier = Token.identifier lexer -- parses an identifier
reserved   = Token.reserved   lexer -- parses a reserved name
reservedOp = Token.reservedOp lexer -- parses an operator
parens     = Token.parens     lexer -- parses surrounding parenthesis
braces     = Token.braces     lexer -- parses surrounding braces
brackets   = Token.brackets   lexer -- parses surrounding brackets
integer    = Token.integer    lexer -- parses an integer
semi       = Token.semi       lexer -- parses a semicolon
comma      = Token.comma      lexer -- parses a comma
colon      = Token.comma      lexer -- parses a colon
whiteSpace = Token.whiteSpace lexer -- parses whitespace

parser :: Parser [Declr]
parser = whiteSpace >> sequenceOfDeclr

sequenceOfDeclr = sepBy function whiteSpace

function :: Parser Declr
function =
  do pos  <- getPosition
     reserved "function"
     var  <- identifier
     args <- parens $ sepBy identifier comma
     stmt <- braces sequenceOfStmt
     return $ FunctionDeclr pos var Nothing Nothing args stmt

sequenceOfStmt :: Parser Stmt
sequenceOfStmt =
  do pos  <- getPosition
     list <- (sepEndBy statement whiteSpace)
     return $ SeqStmt pos list

statement :: Parser Stmt
statement =  ifElseStatement
         <|> whileStatement
         <|> doWhileStatement
         <|> forkStatement
         <|> assignStatement
         <|> otherAssignStatement
         <|> returnStatement
         <|> skipStatement

ifElseStatement :: Parser Stmt
ifElseStatement =
  do pos  <- getPosition
     reserved "if"
     cond  <- parens bExpression
     stmt1 <- braces sequenceOfStmt
     e     <- optionMaybe $ reserved "else"
     case e of
       Nothing -> return $ IfElseStmt pos cond stmt1 (SkipStmt pos)
       Just l -> do stmt2 <- braces sequenceOfStmt
                    return $ IfElseStmt pos cond stmt1 stmt2

whileStatement :: Parser Stmt
whileStatement =
  do pos  <- getPosition
     reserved "while"
     cond <- parens bExpression
     stmt <- braces sequenceOfStmt
     return $ WhileStmt pos Nothing cond stmt

doWhileStatement :: Parser Stmt
doWhileStatement =
  do pos  <- getPosition
     reserved "do"
     stmt <- braces sequenceOfStmt
     reserved "while"
     cond <- parens bExpression
     semi
     return $ DoWhileStmt pos Nothing stmt cond

forkStatement :: Parser Stmt
forkStatement =
  do pos  <- getPosition
     reserved "fork"
     fun  <- identifier
     args <- parens $ sepBy aExpression comma
     semi
     return $ ForkStmt pos fun args  

assignStatement :: Parser Stmt
assignStatement =
  do pos   <- getPosition
     expr1 <- brackets aExpression
     reservedOp ":="
     expr2 <- aExpression
     semi
     return $ AssignStmt pos expr1 expr2

otherAssignStatement :: Parser Stmt
otherAssignStatement =
  do pos <- getPosition
     var <- identifier
     args <- optionMaybe $ parens $ sepBy aExpression comma
     case args of
       Nothing -> reservedOp ":=" >> (derefStatement pos var
                                      <|> callStatement pos var
                                      <|> localAssignStatement pos var)
       Just l  -> semi >> return (CallStmt pos Nothing var l)

derefStatement :: SourcePos -> String -> Parser Stmt
derefStatement pos var =
  do expr <- brackets aExpression
     semi
     return $ DerefStmt pos var expr

callStatement :: SourcePos -> String -> Parser Stmt
callStatement pos var =
  do expr <- aExpression
     case expr of
       VarAExpr _ n -> do args <- optionMaybe $ parens $ sepBy aExpression comma
                          semi
                          case args of
                            Nothing -> return $ LocalAssignStmt pos var $ VarAExpr pos n
                            Just l  -> return $ CallStmt pos (Just var) n l
       otherwise    -> semi >> return (LocalAssignStmt pos var expr)

localAssignStatement :: SourcePos -> String -> Parser Stmt
localAssignStatement pos var =
  do expr <- aExpression
     semi
     return $ LocalAssignStmt pos var expr

returnStatement :: Parser Stmt
returnStatement =
  do pos <- getPosition
     reserved "return"
     expr <- optionMaybe aExpression
     semi
     return $ ReturnStmt pos expr

skipStatement :: Parser Stmt
skipStatement = 
  do pos <- getPosition
     reserved "skip"
     semi
     return $ SkipStmt pos

aExpression :: Parser AExpr
aExpression = buildExpressionParser aOperators aTerm

bExpression :: Parser BExpr
bExpression = buildExpressionParser bOperators bTerm

aOperators = [ [Prefix (do { pos <- getPosition; reservedOp "-"; return (NegAExpr pos            )})          ]
             , [Infix  (do { pos <- getPosition; reservedOp "*"; return (BinaryAExpr pos Multiply)}) AssocLeft]
             , [Infix  (do { pos <- getPosition; reservedOp "/"; return (BinaryAExpr pos Divide  )}) AssocLeft]
             , [Infix  (do { pos <- getPosition; reservedOp "+"; return (BinaryAExpr pos Add     )}) AssocLeft]
             , [Infix  (do { pos <- getPosition; reservedOp "-"; return (BinaryAExpr pos Subtract)}) AssocLeft]
             ]
 
bOperators = [ [Prefix (do { pos <- getPosition; reservedOp "not"; return (NotBExpr pos            )})          ]
             , [Infix  (do { pos <- getPosition; reservedOp "and"; return (BinaryBExpr pos And     )}) AssocLeft]
             , [Infix  (do { pos <- getPosition; reservedOp "or" ; return (BinaryBExpr pos Or      )}) AssocLeft]
             ]

aTerm =  parens aExpression
     <|> variable
     <|> intConst

variable =
  do pos <- getPosition
     var  <- identifier
     return $ VarAExpr pos var

intConst =
  do pos <- getPosition
     i   <- integer
     return $ ConstAExpr pos i

bTerm =  parens bExpression
     <|> (do { pos <- getPosition; reserved "true"; return (ConstBExpr pos True)})
     <|> (do { pos <- getPosition; reserved "false"; return (ConstBExpr pos False)})
     <|> rExpression

rExpression =
  do pos <- getPosition
     a1  <- aExpression
     op  <- relation
     a2  <- aExpression
     return $ RBinaryBExpr pos op a1 a2
 
relation =  (reservedOp "=" >> return Equal)
        <|> (reservedOp "!=" >> return NotEqual)
        <|> (reservedOp ">" >> return Greater)
        <|> (reservedOp "<" >> return Less)
        <|> (reservedOp ">=" >> return GreaterOrEqual)
        <|> (reservedOp "<=" >> return LessOrEqual)

parseString :: String -> [Declr]
parseString str =
  case parse parser "" str of
    Left e  -> error $ show e
    Right r -> r
 
parseFile :: String -> IO [Declr]
parseFile file =
  do program  <- readFile file
     case parse parser "" program of
       Left e  -> print e >> fail "parse error"
       Right r -> return r

aExpressionParser :: Parser AExpr
aExpressionParser = whiteSpace >> aExpression

parseAExpression :: String -> AExpr
parseAExpression str =
  case parse aExpressionParser "" str of
    Left e  -> error $ show e
    Right r -> r

bExpressionParser :: Parser BExpr
bExpressionParser = whiteSpace >> bExpression

parseBExpression :: String -> BExpr
parseBExpression str =
  case parse bExpressionParser "" str of
    Left e  -> error $ show e
    Right r -> r

statementParser :: Parser Stmt
statementParser = whiteSpace >> sequenceOfStmt

parseStatement :: String -> Stmt
parseStatement str =
  case parse statementParser "" str of
    Left e  -> error $ show e
    Right r -> r
