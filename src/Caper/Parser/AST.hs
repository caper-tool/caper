module Caper.Parser.AST(
        module Caper.Parser.AST.Code,
        module Caper.Parser.AST.Annotation,
        module Caper.Parser.AST
        ) where

import Data.List
import Text.ParserCombinators.Parsec

import Caper.Parser.AST.Code
import Caper.Parser.AST.Annotation

-- |Declarations
data Declr = FunctionDeclr SourcePos String (Maybe Assrt) (Maybe Assrt) [String] Stmt
           | RegionDeclr SourcePos String [String] [GuardDeclr] [StateInterpretation] [Action]

instance Show Declr where
  show (FunctionDeclr _ n Nothing Nothing args s)       =
    "function " ++ n ++ "(" ++ intercalate ", " args ++ ") { " ++ show s ++ " }"
  show (FunctionDeclr _ n (Just ls) Nothing args s)     =
    "function " ++ n ++ "(" ++ intercalate ", " args ++ ") requires " ++ show ls ++ " { " ++ show s ++ " }"
  show (FunctionDeclr _ n Nothing (Just ls) args s)     =
    "function " ++ n ++ "(" ++ intercalate ", " args ++ ") ensures " ++ show ls ++  " { " ++ show s ++ " } "
  show (FunctionDeclr _ n (Just ls1) (Just ls2) args s) =
    "function " ++ n ++ "(" ++ intercalate ", " args ++ ") requires " ++ show ls1 ++ "; ensures " ++ show ls2 ++ " { " ++ show s ++ " }"
  show (RegionDeclr _ n args guards intrp actions) =
    "region " ++ n ++ "(" ++ intercalate ", " args ++ ") { guards " ++ intercalate " * " (map show guards) ++ "; interpretation { " ++ intercalate "; " (map show intrp) ++ "; } actions { " ++ intercalate "; " (map show actions) ++ "; } }"
