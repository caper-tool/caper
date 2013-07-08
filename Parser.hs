module Parser where

import Debug.Trace
import System.IO
import Control.Monad
import Data.List
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

-- Boolean expressions
data BExpr = BoolConst SourcePos Bool
           | Not SourcePos BExpr
           | BBinary SourcePos BBinOp BExpr BExpr
           | RBinary SourcePos RBinOp AExpr AExpr

-- Binary Boolean Operators
data BBinOp = And
            | Or

-- Relational Operators
data RBinOp = Equal
            | NotEqual
            | Greater
            | Less
            | GreaterOrEqual
            | LessOrEqual

-- Arithmetic Expressions
data AExpr = Var SourcePos String
           | Deref SourcePos AExpr
           | IntConst SourcePos Integer
           | Neg SourcePos AExpr
           | ABinary SourcePos ABinOp AExpr AExpr
           | FunctCall SourcePos String [AExpr]

-- Arithmetic Operations
data ABinOp = Add
            | Subtract
            | Multiply
            | Divide

-- Statements
data Stmt = StmtSeq SourcePos [Stmt]
          | VarDeclr SourcePos [String]
          | Assign SourcePos AExpr AExpr
          | ExprStmt SourcePos AExpr
          | If SourcePos BExpr Stmt Stmt
          | While SourcePos BExpr Stmt
          | DoWhile SourcePos Stmt BExpr
          | Return SourcePos (Maybe AExpr)
          | Break SourcePos
          | Continue SourcePos
          | Skip SourcePos

-- Declarations
data Declr = Function SourcePos String [String] Stmt

instance Show BExpr where
  show (BoolConst _ b)      = show b
  show (Not _ e)            = "not " ++ show e
  show (BBinary _ op e1 e2) = show e1 ++ show op ++ show e2
  show (RBinary _ op e1 e2) = show e1 ++ show op ++ show e2

instance Show BBinOp where
  show And = " and "
  show Or  = " or "

instance Show RBinOp where
  show Equal          = " = "
  show NotEqual       = " != "
  show Greater        = " > "
  show Less           = " < "
  show GreaterOrEqual = " >= "
  show LessOrEqual    = " <= "

instance Show AExpr where
  show (Var _ n)            = n
  show (Deref _ e)          = "[" ++ show e ++ "]"
  show (IntConst _ i)       = show i
  show (Neg _ e)            = "-" ++ show e
  show (ABinary _ op e1 e2) = show e1 ++ show op ++ show e2
  show (FunctCall _ n args) = n ++ "(" ++ intercalate ", " (map show args) ++ ")"

instance Show ABinOp where
  show Add      = " + "
  show Subtract = " - "
  show Multiply = " * "
  show Divide   = " / "

instance Show Stmt where
  show (StmtSeq _ seq)     = intercalate "; " $ map show seq 
  show (VarDeclr _ vars)   = "var " ++ intercalate ", " vars
  show (Assign _ e1 e2)    = show e1 ++ " := " ++ show e2
  show (ExprStmt _ e)      = show e
  show (If _ e s1 s2)      = "if (" ++ show e ++ ") {" ++ show s1 ++ "} else {" ++ show s2 ++ "}"
  show (While _ e s)       = "while (" ++ show e ++ ") {" ++ show s ++ "}"
  show (DoWhile _ s e)     = "do {" ++ show s ++ "} while (" ++ show e ++ ")"
  show (Return _ Nothing)  = "return"
  show (Return _ (Just e)) = "return " ++ show e
  show (Break _)           = "break"
  show (Continue _)        = "continue"
  show (Skip _)            = "skip"

instance Show Declr where
  show (Function _ n args s) = n ++ "(" ++ ") {" ++ show s ++ "}"
 

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
                                     , "predicate"
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
  do pos  <- getPosition
     reserved "function"
     var  <- identifier
     args <- parens $ sepBy identifier comma
     stmt <- braces sequenceOfStmt
     return $ Function pos var args stmt

sequenceOfStmt =
  do pos  <- getPosition
     list <- (sepEndBy statement semi)
     return $ StmtSeq pos list

statement :: Parser Stmt
statement =  ifElseStatement
         <|> whileStatement
         <|> doWhileStatement
         <|> expressionStatement
         <|> varStatement
         <|> breakStatement
         <|> continueStatement
         <|> returnStatement
         <|> skipStatement

ifElseStatement :: Parser Stmt
ifElseStatement =
  do pos  <- getPosition
     reserved "if"
     cond  <- parens bExpression
     stmt1 <- braces sequenceOfStmt
     reserved "else"
     stmt2 <- braces sequenceOfStmt
     return $ If pos cond stmt1 stmt2

whileStatement :: Parser Stmt
whileStatement =
  do pos  <- getPosition
     reserved "while"
     cond <- parens bExpression
     stmt <- braces sequenceOfStmt
     return $ While pos cond stmt

doWhileStatement :: Parser Stmt
doWhileStatement =
  do pos  <- getPosition
     reserved "do"
     stmt <- braces sequenceOfStmt
     reserved "while"
     cond <- parens bExpression
     return $ DoWhile pos stmt cond

expressionStatement :: Parser Stmt
expressionStatement =
  do pos <- getPosition
     expr <- aExpression
     op   <- optionMaybe $ assignStatement
     case op of
       Nothing -> return $ ExprStmt pos expr
       Just l  -> return $ Assign pos expr l

assignStatement :: Parser AExpr
assignStatement =
  do reservedOp ":="
     expr <- aExpression
     return expr

varStatement :: Parser Stmt
varStatement =
  do pos <- getPosition
     reserved "var"
     list <- (sepBy1 identifier comma)
     return $ VarDeclr pos list

returnStatement :: Parser Stmt
returnStatement =
  do pos <- getPosition
     reserved "return"
     expr <- optionMaybe aExpression
     return $ Return pos expr

breakStatement :: Parser Stmt
breakStatement =
  do pos <- getPosition
     reserved "break"
     return $ Break pos

continueStatement :: Parser Stmt
continueStatement =
  do pos <- getPosition
     reserved "continue"
     return $ Continue pos

skipStatement :: Parser Stmt
skipStatement = 
  do pos <- getPosition
     reserved "skip"
     return $ Skip pos

aExpression :: Parser AExpr
aExpression = buildExpressionParser aOperators aTerm

bExpression :: Parser BExpr
bExpression = buildExpressionParser bOperators bTerm

aOperators = [ [Prefix (do { pos <- getPosition; reservedOp "-"; return (Neg pos             )})          ]
             , [Infix  (do { pos <- getPosition; reservedOp "*"; return (ABinary pos Multiply)}) AssocLeft]
             , [Infix  (do { pos <- getPosition; reservedOp "/"; return (ABinary pos Divide  )}) AssocLeft]
             , [Infix  (do { pos <- getPosition; reservedOp "+"; return (ABinary pos Add     )}) AssocLeft]
             , [Infix  (do { pos <- getPosition; reservedOp "-"; return (ABinary pos Subtract)}) AssocLeft]
             ]
 
bOperators = [ [Prefix (do { pos <- getPosition; reservedOp "not"; return (Not pos             )})          ]
             , [Infix  (do { pos <- getPosition; reservedOp "and"; return (BBinary pos And     )}) AssocLeft]
             , [Infix  (do { pos <- getPosition; reservedOp "or" ; return (BBinary pos Or      )}) AssocLeft]
             ]

aTerm =  parens aExpression
     <|> funCallOrVar
     <|> deref
     <|> intConst

funCallOrVar =
  do pos <- getPosition
     var  <- identifier
     list <- optionMaybe $ parens $ sepBy aExpression comma
     case list of
       Nothing -> return $ Var pos var
       Just l  -> return $ FunctCall pos var l

deref =
  do pos <- getPosition
     e   <- brackets aExpression
     return $ Deref pos e

intConst =
  do pos <- getPosition
     i   <- integer
     return $ IntConst pos i

bTerm =  parens bExpression
     <|> (do { pos <- getPosition; reserved "true"; return (BoolConst pos True)})
     <|> (do { pos <- getPosition; reserved "false"; return (BoolConst pos False)})
     <|> rExpression

rExpression =
  do pos <- getPosition
     a1 <- aExpression
     op <- relation
     a2 <- aExpression
     return $ RBinary pos op a1 a2
 
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
