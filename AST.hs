module AST where

import Data.List
import Text.ParserCombinators.Parsec

-- Boolean expressions
data BExpr = ConstBExpr SourcePos Bool
           | NotBExpr SourcePos BExpr
           | BinaryBExpr SourcePos BBinOp BExpr BExpr
           | RBinaryBExpr SourcePos RBinOp AExpr AExpr

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
data AExpr = VarAExpr SourcePos String
           | DerefAExpr SourcePos AExpr
           | ConstAExpr SourcePos Integer
           | NegAExpr SourcePos AExpr
           | BinaryAExpr SourcePos ABinOp AExpr AExpr
           | CallAExpr SourcePos String [AExpr]

-- Arithmetic Operations
data ABinOp = Add
            | Subtract
            | Multiply
            | Divide

-- Statements
data Stmt = StmtSeq SourcePos [Stmt]
          | VarStmt SourcePos [String]
          | AssignStmt SourcePos AExpr AExpr
          | ExprStmt SourcePos AExpr
          | IfElseStmt SourcePos BExpr Stmt Stmt
          | WhileStmt SourcePos (Maybe LStmt) BExpr Stmt
          | DoWhileStmt SourcePos (Maybe LStmt) Stmt BExpr
          | ReturnStmt SourcePos (Maybe AExpr)
          | SkipStmt SourcePos
          | AssertStmt SourcePos LStmt

data LStmt = MapsTo SourcePos AExpr AExpr

-- Declarations
data Declr = FunctionDeclr SourcePos String (Maybe LStmt) (Maybe LStmt) [String] Stmt

instance Show BExpr where
  show (ConstBExpr _ b)      = show b
  show (NotBExpr _ e)            = "(" ++ "not " ++ show e ++ ")"
  show (BinaryBExpr _ op e1 e2) = "(" ++ show e1 ++ show op ++ show e2 ++ ")"
  show (RBinaryBExpr _ op e1 e2) = "(" ++ show e1 ++ show op ++ show e2 ++ ")"

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
  show (VarAExpr _ n)            = n
  show (DerefAExpr _ e)          = "[" ++ show e ++ "]"
  show (ConstAExpr _ i)       = show i
  show (NegAExpr _ e)            = "-" ++ show e
  show (BinaryAExpr _ op e1 e2) = "(" ++ show e1 ++ show op ++ show e2 ++ ")"
  show (CallAExpr _ n args) = n ++ "(" ++ intercalate ", " (map show args) ++ ")"

instance Show ABinOp where
  show Add      = " + "
  show Subtract = " - "
  show Multiply = " * "
  show Divide   = " / "

instance Show Stmt where
  show (StmtSeq _ seq)               = unwords $ map show seq 
  show (VarStmt _ vars)              = "var " ++ intercalate ", " vars ++ ";"
  show (AssignStmt _ e1 e2)          = show e1 ++ " := " ++ show e2 ++ ";"
  show (ExprStmt _ e)                = show e ++ ";"
  show (IfElseStmt _ e s1 s2)        = "if (" ++ show e ++ ") {" ++ show s1 ++ "} else {" ++ show s2 ++ "}"
  show (WhileStmt _ Nothing e s)     = "while (" ++ show e ++ ") {" ++ show s ++ "}"
  show (WhileStmt _ (Just ls) e s)   = "while (" ++ show e ++ ") {" ++ show s ++ "}"
  show (DoWhileStmt _ Nothing s e)   = "do {" ++ show s ++ "} while (" ++ show e ++ ")"
  show (DoWhileStmt _ (Just ls) s e) = "do {" ++ show s ++ "} while (" ++ show e ++ ")"
  show (ReturnStmt _ Nothing)        = "return;"
  show (ReturnStmt _ (Just e))       = "return " ++ show e ++ ";"
  show (SkipStmt _)                  = "skip;"
  show (AssertStmt _ ls)             = "assert " ++ show ls ++ ";"

instance Show LStmt where
  show (MapsTo _ e1 e2) = show e1 ++ " |-> " ++ show e2;

instance Show Declr where
  show (FunctionDeclr _ n Nothing Nothing args s)       =
    n ++ "(" ++ intercalate ", " args ++ ") {" ++ show s ++ "}"
  show (FunctionDeclr _ n (Just ls) Nothing args s)     =
    n ++ "(" ++ intercalate ", " args ++ ") requires " ++ show ls ++ " {" ++ show s ++ "}"
  show (FunctionDeclr _ n Nothing (Just ls) args s)     =
    n ++ "(" ++ intercalate ", " args ++ ") ensures " ++ show ls ++  " {" ++ show s ++ "}"
  show (FunctionDeclr _ n (Just ls1) (Just ls2) args s) =
    n ++ "(" ++ intercalate ", " args ++ ") requires " ++ show ls1 ++ "; ensures " ++ show ls2 ++ " {" ++ show s ++ "}"
