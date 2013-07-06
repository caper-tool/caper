module Parser where

import System.IO
import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

-- Boolean expressions
data BExpr = BoolConst Bool
           | Not BExpr
           | BBinary BBinOp BExpr BExpr
           | RBinary RBinOp AExpr AExpr
             deriving (Show)

-- Binary Boolean Operators
data BBinOp = And
            | Or
              deriving (Show)

-- Relational Operators
data RBinOp = Equal
            | NotEqual
            | Greater
            | Less
            | GreaterOrEqual
            | LessOrEqual
              deriving (Show)

-- Arithmetic Expressions
data AExpr = Var String
           | IntConst Integer
           | Neg AExpr
           | ABinary ABinOp AExpr AExpr
             deriving (Show)

-- Arithmetic Operations
data ABinOp = Add
            | Subtract
            | Multiply
            | Divide
              deriving (Show)

-- Statements
data Stmt = Seq [Stmt]
          | Assign String AExpr
          | If BExpr Stmt Stmt
          | While BExpr Stmt
          | DoWhile Stmt BExpr
          | Skip
            deriving (Show)

languageDef =
  emptyDef { Token.commentStart    = "/*"
           , Token.commentEnd      = "*/"
           , Token.commentLine     = "//"
           , Token.identStart      = letter
           , Token.identLetter     = alphaNum
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
                                     , "local"
                                     , "return"
                                     , "break"
                                     , "("
                                     , ")"
                                     , "{"
                                     , "}"
                                     ]
           , Token.reservedOpNames = ["+", "-", "*", "/", ":="
                                     , "=", "!=", "<", ">", ">=", "<="
                                     , "and", "or", "not"
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
whiteSpace = Token.whiteSpace lexer -- parses whitespace

parser :: Parser Stmt
parser = whiteSpace >> sequenceOfStmt

sequenceOfStmt =
  do list <- (sepBy1 statement semi)
     -- If there's only one statement return it without using Seq.
     return $ Seq list --if length list == 1 then head list else Seq list

statement :: Parser Stmt
statement =   ifStmt
          <|> whileStmt
          <|> doWhileStmt
          <|> skipStmt
          <|> assignStmt

ifStmt :: Parser Stmt
ifStmt =
  do reserved "if"
     cond  <- parens bExpression
     stmt1 <- braces statement
     reserved "else"
     stmt2 <- braces statement
     return $ If cond stmt1 stmt2

whileStmt :: Parser Stmt
whileStmt =
  do reserved "while"
     cond <- parens bExpression
     stmt <- braces statement
     return $ While cond stmt

doWhileStmt :: Parser Stmt
doWhileStmt =
  do reserved "do"
     stmt <- braces statement
     reserved "while"
     cond <- parens bExpression
     return $ DoWhile stmt cond

assignStmt :: Parser Stmt
assignStmt =
  do var  <- identifier
     reservedOp ":="
     expr <- aExpression
     return $ Assign var expr

skipStmt :: Parser Stmt
skipStmt = reserved "skip" >> return Skip

aExpression :: Parser AExpr
aExpression = buildExpressionParser aOperators aTerm
 
bExpression :: Parser BExpr
bExpression = buildExpressionParser bOperators bTerm

aOperators = [ [Prefix (reservedOp "-"   >> return (Neg             ))          ]
             , [Infix  (reservedOp "*"   >> return (ABinary Multiply)) AssocLeft]
             , [Infix  (reservedOp "/"   >> return (ABinary Divide  )) AssocLeft]
             , [Infix  (reservedOp "+"   >> return (ABinary Add     )) AssocLeft]
             , [Infix  (reservedOp "-"   >> return (ABinary Subtract)) AssocLeft]
              ]
 
bOperators = [ [Prefix (reservedOp "not" >> return (Not             ))          ]
             , [Infix  (reservedOp "and" >> return (BBinary And     )) AssocLeft]
             , [Infix  (reservedOp "or"  >> return (BBinary Or      )) AssocLeft]
             ]

aTerm =  parens aExpression
     <|> liftM Var identifier
     <|> liftM IntConst integer

bTerm =  parens bExpression
     <|> (reserved "true"  >> return (BoolConst True ))
     <|> (reserved "false" >> return (BoolConst False))
     <|> rExpression

rExpression =
  do a1 <- aExpression
     op <- relation
     a2 <- aExpression
     return $ RBinary op a1 a2
 
relation =   (reservedOp ">" >> return Greater)
         <|> (reservedOp "<" >> return Less)

parseString :: String -> Stmt
parseString str =
  case parse parser "" str of
    Left e  -> error $ show e
    Right r -> r
 
parseFile :: String -> IO Stmt
parseFile file =
  do program  <- readFile file
     case parse parser "" program of
       Left e  -> print e >> fail "parse error"
       Right r -> return r
