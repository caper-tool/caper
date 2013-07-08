module Parser where

import Debug.Trace
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
           | Deref AExpr
           | IntConst Integer
           | Cond BExpr AExpr AExpr
           | Neg AExpr
           | ABinary ABinOp AExpr AExpr
           | FunctCall String [AExpr]
             deriving (Show)

-- Arithmetic Operations
data ABinOp = Add
            | Subtract
            | Multiply
            | Divide
              deriving (Show)

-- Statements
data Stmt = StmtSeq [Stmt]
          | VarDeclr [String]
          | Assign AExpr AExpr
          | ExprStmt AExpr
          | If BExpr Stmt Stmt
          | While BExpr Stmt
          | DoWhile Stmt BExpr
          | Return (Maybe AExpr)
          | Break
          | Continue
          | Skip
            deriving (Show)

-- Declarations
data Declr = Function String [String] Stmt
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
                                     , "var"
                                     , "return"
                                     , "break"
                                     , "continue"
                                     , "function"
                                     , "region"
                                     , "("
                                     , ")"
                                     , "{"
                                     , "}"
                                     , "]"
                                     , "["
                                     ]
           , Token.reservedOpNames = ["+", "-", "*", "/", ":="
                                     , "=", "!=", "<", ">", ">=", "<="
                                     , "and", "or", "not", "?", ":"
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
  do reserved "function"
     var  <- identifier
     args <- parens $ sepBy identifier comma
     stmt <- braces sequenceOfStmt
     return $ Function var args stmt

sequenceOfStmt =
  do list <- (sepEndBy statement semi)
     return $ StmtSeq list

statement :: Parser Stmt
statement =  ifStatement
         <|> ifElseStatement
         <|> whileStatement
         <|> doWhileStatement
         <|> expressionStatement
         <|> varStatement
         <|> breakStatement
         <|> continueStatement
         <|> returnStatement
         <|> skipStatement

ifStatement :: Parser Stmt
ifStatement =
  do reserved "if"
     cond  <- parens bExpression
     stmt1 <- braces sequenceOfStmt
     return $ If cond stmt1 Skip

ifElseStatement :: Parser Stmt
ifElseStatement =
  do reserved "if"
     cond  <- parens bExpression
     stmt1 <- braces sequenceOfStmt
     reserved "else"
     stmt2 <- braces sequenceOfStmt
     return $ If cond stmt1 stmt2

whileStatement :: Parser Stmt
whileStatement =
  do reserved "while"
     cond <- parens bExpression
     stmt <- braces sequenceOfStmt
     return $ While cond stmt

doWhileStatement :: Parser Stmt
doWhileStatement =
  do reserved "do"
     stmt <- braces sequenceOfStmt
     reserved "while"
     cond <- parens bExpression
     return $ DoWhile stmt cond

expressionStatement :: Parser Stmt
expressionStatement =
  do expr <- aExpression
     op   <- optionMaybe $ assignStatement
     case op of
       Nothing -> return $ ExprStmt expr
       Just l  -> return $ Assign expr l

assignStatement :: Parser AExpr
assignStatement =
  do reservedOp ":="
     expr <- aExpression
     return expr

varStatement :: Parser Stmt
varStatement =
  do reserved "var"
     list <- (sepBy1 identifier comma)
     return $ VarDeclr list

returnStatement :: Parser Stmt
returnStatement =
  do reserved "return"
     expr <- optionMaybe aExpression
     return $ Return expr

breakStatement :: Parser Stmt
breakStatement = reserved "break" >> return Break

continueStatement :: Parser Stmt
continueStatement = reserved "continue" >> return Continue

skipStatement :: Parser Stmt
skipStatement = reserved "skip" >> return Skip

aExpression :: Parser AExpr
aExpression = --try (condExpression)
           buildExpressionParser aOperators aTerm

condExpression :: Parser AExpr
condExpression =
  do cond  <- bExpression
     reservedOp "?"
     expr1 <- aExpression
     reservedOp ":"
     expr2 <- aExpression
     return $ Cond cond expr1 expr2

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
     <|> funCallOrVar
     <|> liftM Deref (brackets aExpression)
     <|> liftM IntConst integer

funCallOrVar =
  do var  <- identifier
     list <- optionMaybe $ parens $ sepBy aExpression comma
     case list of
       Nothing -> return $ Var var
       Just l  -> return $ FunctCall var l

bTerm =  parens bExpression
     <|> (reserved "true"  >> return (BoolConst True ))
     <|> (reserved "false" >> return (BoolConst False))
     <|> rExpression

rExpression =
  do a1 <- aExpression
     op <- relation
     a2 <- aExpression
     return $ RBinary op a1 a2
 
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
