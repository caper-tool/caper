module Caper.Parser.AST(
        module Caper.Parser.AST.Code,
        module Caper.Parser.AST.Annotation,
        module Caper.Parser.AST
        ) where

import Data.List
import Text.ParserCombinators.Parsec
import Data.Maybe

import Caper.Parser.AST.Code
import Caper.Parser.AST.Annotation
import Caper.ExceptionContext

data FunctionDeclr = FunctionDeclr SourcePos String (Maybe Assrt) (Maybe Assrt) [String] Stmt
data RegionDeclr = RegionDeclr SourcePos String [String] TopLevelGuardDeclr [StateInterpretation] [Action]
data PredicateDeclr = PredicateDeclr SourcePos String [TVarExpr]

-- |Declarations
data Declr = DeclrFun FunctionDeclr | DeclrReg RegionDeclr | DeclrPred PredicateDeclr

instance Show FunctionDeclr where
  show (FunctionDeclr _ n Nothing Nothing args s)       =
    "function " ++ n ++ "(" ++ intercalate ", " args ++ ") { " ++ show s ++ " }"
  show (FunctionDeclr _ n (Just ls) Nothing args s)     =
    "function " ++ n ++ "(" ++ intercalate ", " args ++ ") requires " ++ show ls ++ " { " ++ show s ++ " }"
  show (FunctionDeclr _ n Nothing (Just ls) args s)     =
    "function " ++ n ++ "(" ++ intercalate ", " args ++ ") ensures " ++ show ls ++  " { " ++ show s ++ " } "
  show (FunctionDeclr _ n (Just ls1) (Just ls2) args s) =
    "function " ++ n ++ "(" ++ intercalate ", " args ++ ") requires " ++ show ls1 ++ "; ensures " ++ show ls2 ++ " { " ++ show s ++ " }"

instance Show RegionDeclr where
  show (RegionDeclr _ n args guards intrp actions) =
    "region " ++ n ++ "(" ++ intercalate ", " args ++ ") { guards " ++ show guards ++ "; interpretation { " ++ intercalate "; " (map show intrp) ++ "; } actions { " ++ intercalate "; " (map show actions) ++ "; } }"

instance Show PredicateDeclr where
  show (PredicateDeclr _ n args) =
    "predicate " ++ n ++ "(" ++ intercalate ", " (map show args) ++ ");"
  
instance Show Declr where
    show (DeclrFun f) = show f
    show (DeclrReg r) = show r
    show (DeclrPred p) = show p

instance Contextual FunctionDeclr where
  toContext (FunctionDeclr sp nm _ _ _ _) = DescriptiveContext sp $
        "In the function named '" ++ nm ++ "'"

instance Contextual RegionDeclr where    
  toContext (RegionDeclr sp nm _ _ _ _) = DescriptiveContext sp $
        "In the declaration of region type '" ++ nm ++ "'"

instance Contextual PredicateDeclr where
  toContext (PredicateDeclr sp nm _) = DescriptiveContext sp $
        "In the declaration of predicate '" ++ nm ++ "'"

instance Contextual Declr where
  toContext (DeclrFun f) = toContext f
  toContext (DeclrReg r) = toContext r
  toContext (DeclrPred p) = toContext p

functionDeclrs :: [Declr] -> [FunctionDeclr]
functionDeclrs = mapMaybe funs
    where
        funs (DeclrFun f) = Just f
        funs _ = Nothing

regionDeclrs :: [Declr] -> [RegionDeclr]
regionDeclrs = mapMaybe regs
    where
        regs (DeclrReg r) = Just r
        regs _ = Nothing

predicateDeclrs :: [Declr] -> [PredicateDeclr]
predicateDeclrs = mapMaybe preds
    where
        preds (DeclrPred p) = Just p
        preds _ = Nothing
