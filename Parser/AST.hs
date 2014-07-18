module Parser.AST where

import Data.List
import Text.ParserCombinators.Parsec


-- * Program syntax

-- Boolean expressions
data BExpr = ConstBExpr SourcePos Bool
           | NotBExpr SourcePos BExpr
           | BinaryBExpr SourcePos BBinOp BExpr BExpr
           | RBinaryBExpr SourcePos BinRel AExpr AExpr

-- Binary Boolean Operators
data BBinOp = Or
            | And
            deriving (Eq)

-- Relational Operators
data BinRel = Equal
            | NotEqual
            | Greater
            | GreaterOrEqual
            | Less
            | LessOrEqual
            deriving (Eq)

-- Arithmetic Expressions
data AExpr = VarAExpr SourcePos String
           | ConstAExpr SourcePos Integer
           | NegAExpr SourcePos AExpr
           | BinaryAExpr SourcePos ABinOp AExpr AExpr

-- Arithmetic Operations
data ABinOp = Add
            | Subtract
            | Multiply
            | Divide
            deriving (Eq)

-- Statements
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


-- * Assertion syntax

-- |(Optional) variable expressions
data VarExpr = Variable SourcePos String  -- ^A logical variable
             | WildCard SourcePos         -- ^A wildcard
instance Show VarExpr where
        show (Variable _ s) = s
        show (WildCard _) = "_"

-- |Value Expressions
data ValExpr = VarValExpr SourcePos VarExpr                     -- ^Variable
             | ConstValExpr SourcePos Integer                   -- ^Integer constant
             | UnaryValExpr SourcePos ValUnOp ValExpr           -- ^Unary operator
             | BinaryValExpr SourcePos ValBinOp ValExpr ValExpr -- ^Binary operator
             | SetValExpr SourcePos [ValExpr]                   -- ^Set-of-values expression
instance Show ValExpr where
        show (VarValExpr _ ve) = show ve
        show (ConstValExpr _ c) = show c
        show (UnaryValExpr _ uo ve) = show uo ++ show ve
        show (BinaryValExpr _ bo ve1 ve2) = "(" ++ show ve1 ++ show bo ++ show ve2 ++ ")"
        show (SetValExpr _ ves) = "{" ++ intercalate "," (map show ves) ++ "}"

-- |Unary value operator
data ValUnOp = ValNegation -- ^Unary minus
                deriving (Eq)
instance Show ValUnOp where
        show ValNegation = "-"

-- |Binary value operators
data ValBinOp = ValAdd          -- ^Addition
              | ValSubtract     -- ^Subtraction
              | ValMultiply     -- ^Multiplication
              | ValDivide       -- ^Division
              deriving (Eq)
instance Show ValBinOp where
        show ValAdd = "+"
        show ValSubtract = "-"
        show ValMultiply = "*"
        show ValDivide = "/"

-- |(Dis)equality binary relations.
data EqBinRel = EqualRel        -- ^@=@
              | NotEqualRel     -- ^@!=@
              deriving (Eq)
instance Show EqBinRel where
        show EqualRel = "="
        show NotEqualRel = "!="

-- |Binary value relations
data ValBinRel = ValEquality EqBinRel   -- ^(Dis)equality
               | ValGreater             -- ^@>@
               | ValGreaterOrEqual      -- ^@>=@
               | ValLess                -- ^@<@
               | ValLessOrEqual         -- ^@<=@
               deriving (Eq)
instance Show ValBinRel where
        show (ValEquality vo) = show vo
        show ValGreater = ">"
        show ValGreaterOrEqual = ">="
        show ValLess = "<"
        show ValLessOrEqual = "<="

-- |Permission expressions
data PermExpr = VarPermExpr SourcePos VarExpr                           -- ^Variable
              | ConstPermExpr SourcePos PermConst                       -- ^Constant
              | UnaryPermExpr SourcePos PermUnOp PermExpr               -- ^Unary operator
              | BinaryPermExpr SourcePos PermBinOp PermExpr PermExpr    -- ^Binary operator
instance Show PermExpr where
        show (VarPermExpr _ ve) = show ve
        show (ConstPermExpr _ pc) = show pc
        show (UnaryPermExpr _ uo pe) = show uo ++ show pe
        show (BinaryPermExpr _ bo pe1 pe2) = "(" ++ show pe1 ++ show bo ++ show pe2 ++ ")"

-- |Permission constants.
data PermConst = FullPerm
               | EmptyPerm
               deriving (Eq)
instance Show PermConst where
        show FullPerm = "1p"
        show EmptyPerm = "0p"

-- |Unary permission operator.
data PermUnOp = Complement
                deriving (Eq)
instance Show PermUnOp where
        show Complement = "~"

-- |Binary permission operator.
data PermBinOp = Composition
                deriving (Eq)
instance Show PermBinOp where
        show Composition = "$"

-- |Binary permission relations.
data PermBinRel = PermEquality EqBinRel
                | Compatible
                deriving (Eq)
instance Show PermBinRel where
        show (PermEquality pe) = show pe
        show Compatible = "#"

-- |Pure assertions
data PureAssrt = ConstBAssrt SourcePos Bool                             -- ^Boolean constant
               | NotBAssrt SourcePos PureAssrt                          -- ^Boolean /not/
               | BinaryVarAssrt SourcePos EqBinRel VarExpr VarExpr      -- ^Variable (dis)equality
               | BinaryValAssrt SourcePos ValBinRel ValExpr ValExpr     -- ^Value binary predicates
               | BinaryPermAssrt SourcePos PermBinRel PermExpr PermExpr -- ^Permission binary predicates
instance Show PureAssrt where
        show (ConstBAssrt _ b) = if b then "true" else "false"
        show (NotBAssrt _ pe) = "!" ++ show pe
        show (BinaryVarAssrt _ br e1 e2) = show e1 ++ show br ++ show e2
        show (BinaryValAssrt _ br e1 e2) = show e1 ++ show br ++ show e2
        show (BinaryPermAssrt _ br e1 e2) = show e1 ++ show br ++ show e2

-- |Basic heap assertions
data CellAssrt = Cell SourcePos ValExpr ValExpr         -- ^ Single cell: @/x/ |-> /y/@
               | CellBlock SourcePos ValExpr ValExpr    -- ^ Block of cells: @/x/ |-> #cells(/y/)@
instance Show CellAssrt where
        show (Cell _ e1 e2) = show e1 ++ " |-> " ++ show e2
        show (CellBlock _ e1 e2) = show e1 ++ " |-> #cells(" ++ show e2 ++ ")"

data AnyExpr = AnyVar VarExpr | AnyVal ValExpr | AnyPerm PermExpr
instance Show AnyExpr where
        show (AnyVar e) = show e
        show (AnyVal e) = show e
        show (AnyPerm e) = show e

-- |Region assertions
data RegionAssrt = Region {
        regionAssrtSourcePos :: SourcePos,      -- ^Source location of syntax
        regionAssrtType :: String,              -- ^Region type name
        regionAssrtVariable :: String,          -- ^Region identifier variable
        regionAssrtArguments :: [AnyExpr],      -- ^List of region parameters
        regionAssrtState :: ValExpr             -- ^Region state
        }
instance Show RegionAssrt where
        show (Region _ t v args s) = t ++ "(" ++ v ++ concat (map ((',' :) . show) args) ++ "," ++ show s ++ ")"

-- |Predicate assertions
data Predicate = Predicate SourcePos String [AnyExpr]
instance Show Predicate where
        show (Predicate _ p args) = p ++ "(" ++ intercalate "," (map show args) ++ ")"

-- |Guard assertions
data Guard = NamedGuard SourcePos String                  -- ^Simple named guard
           | PermGuard SourcePos String PermExpr          -- ^Guard with permission
           | ParamGuard SourcePos String [PermExpr]       -- ^Parametrised guard
instance Show Guard where
        show (NamedGuard _ n) = n
        show (PermGuard _ n pe) = n ++ "[" ++ show pe ++ "]"
        show (ParamGuard _ n paras) = n ++ "(" ++ intercalate "," (map show paras) ++ ")"

-- |Guards associated with a region
data Guards = Guards SourcePos String [Guard]
instance Show Guards where
        show (Guards _ id gds) = id ++ "@(" ++ intercalate " * " (map show gds) ++ ")"


-- |Spatial assertion
data SpatialAssrt = SARegion RegionAssrt
                  | SAPredicate Predicate
                  | SACell CellAssrt
                  | SAGuards Guards
instance Show SpatialAssrt where
        show (SARegion a) = show a
        show (SAPredicate a) = show a
        show (SACell a) = show a
        show (SAGuards a) = show a

-- |Assertions
data Assrt = AssrtPure SourcePos PureAssrt
           | AssrtSpatial SourcePos SpatialAssrt
           | AssrtConj SourcePos Assrt Assrt
           | AssrtITE SourcePos PureAssrt Assrt Assrt
instance Show Assrt where
        show (AssrtPure _ a) = show a
        show (AssrtSpatial _ a) = show a
        show (AssrtConj _ a1 a2) = show a1 ++ " &*& " ++ show a2
        show (AssrtITE _ ac a1 a2) = "(" ++ show ac ++ " ? " ++ show a1 ++ " : " ++ show a2 ++ ")"

-- |Declarations
data Declr = FunctionDeclr SourcePos String (Maybe Assrt) (Maybe Assrt) [String] Stmt

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


instance Show Declr where
  show (FunctionDeclr _ n Nothing Nothing args s)       =
    "function " ++ n ++ "(" ++ intercalate ", " args ++ ") {" ++ show s ++ "}"
  show (FunctionDeclr _ n (Just ls) Nothing args s)     =
    "function " ++ n ++ "(" ++ intercalate ", " args ++ ") requires " ++ show ls ++ " {" ++ show s ++ "}"
  show (FunctionDeclr _ n Nothing (Just ls) args s)     =
    "function " ++ n ++ "(" ++ intercalate ", " args ++ ") ensures " ++ show ls ++  " {" ++ show s ++ "}"
  show (FunctionDeclr _ n (Just ls1) (Just ls2) args s) =
    "function " ++ n ++ "(" ++ intercalate ", " args ++ ") requires " ++ show ls1 ++ "; ensures " ++ show ls2 ++ " {" ++ show s ++ "}"
