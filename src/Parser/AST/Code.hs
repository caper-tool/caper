module Parser.AST.Code where

import Parser.AST.Annotation
import Data.List
import Text.ParserCombinators.Parsec
-- * Program syntax

-- |Boolean expressions
data BExpr = ConstBExpr SourcePos Bool
           | NotBExpr SourcePos BExpr
           | BinaryBExpr SourcePos BBinOp BExpr BExpr
           | RBinaryBExpr SourcePos BinRel AExpr AExpr

-- |Binary Boolean Operators
data BBinOp = Or
            | And
            deriving (Eq)

-- |Relational Operators
data BinRel = Equal
            | NotEqual
            | Greater
            | GreaterOrEqual
            | Less
            | LessOrEqual
            deriving (Eq)

-- |Arithmetic Expressions
data AExpr = VarAExpr SourcePos String
           | ConstAExpr SourcePos Integer
           | NegAExpr SourcePos AExpr
           | BinaryAExpr SourcePos ABinOp AExpr AExpr

-- |Arithmetic Operations
data ABinOp = Add
            | Subtract
            | Multiply
            | Divide
            deriving (Eq)

-- |Statements
data Stmt = SeqStmt SourcePos [Stmt]
          | IfElseStmt SourcePos BExpr Stmt Stmt
          | WhileStmt SourcePos (Maybe Assrt) BExpr Stmt
          | DoWhileStmt SourcePos (Maybe Assrt) Stmt BExpr
          | LocalAssignStmt SourcePos String AExpr
          | DerefStmt SourcePos String AExpr
          | AssignStmt SourcePos AExpr AExpr
          | CallStmt SourcePos (Maybe String) String [AExpr]
          | ReturnStmt SourcePos (Maybe AExpr)
          | SkipStmt SourcePos
          | ForkStmt SourcePos String [AExpr]
          | AssertStmt SourcePos Assrt

instance Show BExpr where
  show (ConstBExpr _ b)          = show b
  show (NotBExpr _ e)            = "(" ++ "not " ++ show e ++ ")"
  show (BinaryBExpr _ op e1 e2)  = "(" ++ show e1 ++ show op ++ show e2 ++ ")"
  show (RBinaryBExpr _ op e1 e2) = "(" ++ show e1 ++ show op ++ show e2 ++ ")"

instance Show BBinOp where
  show Or  = " or "
  show And = " and "

instance Show BinRel where
  show Equal          = " = "
  show NotEqual       = " != "
  show Greater        = " > "
  show GreaterOrEqual = " >= "
  show Less           = " <"
  show LessOrEqual    = " <= "

instance Show AExpr where
  show (VarAExpr _ n)           = n
  show (ConstAExpr _ i)         = show i
  show (NegAExpr _ e)           = "-" ++ show e
  show (BinaryAExpr _ op e1 e2) = "(" ++ show e1 ++ show op ++ show e2 ++ ")"

instance Show ABinOp where
  show Add      = " + "
  show Subtract = " - "
  show Multiply = " * "
  show Divide   = " / "

instance Show Stmt where
  show (SeqStmt _ seq)               = unwords $ map show seq 
  show (IfElseStmt _ e s1 s2)        = "if (" ++ show e ++ ") {" ++ show s1 ++ "} else {" ++ show s2 ++ "}"
  show (WhileStmt _ Nothing e s)     = "while (" ++ show e ++ ") {" ++ show s ++ "}"
  show (WhileStmt _ (Just ls) e s)   = "while (" ++ show e ++ ") {" ++ show s ++ "}"
  show (DoWhileStmt _ Nothing s e)   = "do {" ++ show s ++ "} while (" ++ show e ++ ");"
  show (DoWhileStmt _ (Just ls) s e) = "do {" ++ show s ++ "} while (" ++ show e ++ ");"
  show (LocalAssignStmt _ n e)       = n ++ " := " ++ show e ++ ";"
  show (DerefStmt _ n e)             = n ++ " := [" ++ show e ++ "];"  
  show (AssignStmt _ e1 e2)          = "[" ++ show e1 ++ "] := " ++ show e2 ++ ";"
  show (CallStmt _ Nothing n2 es)    = n2 ++ "(" ++ intercalate ", " (map show es) ++ ");"
  show (CallStmt _ (Just n1) n2 es)  = n1 ++ " := " ++ n2 ++ "(" ++ intercalate ", " (map show es) ++ ");"
  show (ReturnStmt _ Nothing)        = "return;"
  show (ReturnStmt _ (Just e))       = "return " ++ show e ++ ";"
  show (SkipStmt _)                  = "skip;"
  show (ForkStmt _ n es)             = "fork " ++ n ++ "(" ++ intercalate ", " (map show es) ++ ");"
  show (AssertStmt _ ls)             = "assert " ++ show ls ++ ";"

