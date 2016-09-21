module Caper.Procedures where

import qualified Data.Map as Map
import Data.Foldable
import Control.Lens

import Caper.Constants
import Caper.Exceptions
import Caper.Logger
import Caper.Parser.AST
import Text.Parsec (SourcePos)


data Specification = Specification {
        specParams :: [String],
        specPrecondition :: Assrt,
        specPostcondition :: Assrt
        }

class SpecificationContext c where
    specifications :: Getter c (Map.Map String Specification)


defaultPrecondition :: SourcePos -> Assrt
defaultPrecondition sp = AssrtPure sp $ ConstBAssrt sp defaultPreconditionBool

defaultPostcondition :: SourcePos -> Assrt
defaultPostcondition sp = AssrtPure sp $ ConstBAssrt sp defaultPostconditionBool

-- TODO: Somewhere we should check that procedures don't have multiple arguments of the same name 

declrsToProcedureSpecs :: (MonadRaise m, MonadLogger m) =>
                [FunctionDeclr] -> m (Map.Map String Specification)
declrsToProcedureSpecs = foldlM declrSpec Map.empty
        where
            declrSpec mp fdec@(FunctionDeclr sp fname prec post params _) = contextualise fdec $
                                        case Map.lookup fname mp of
                                            (Just _) -> raise $ OverloadedProcedure fname
                                            Nothing -> do
                                                pre' <- case prec of
                                                    Just x -> return x
                                                    Nothing -> do
                                                        let def = defaultPrecondition sp
                                                        logEvent $ WarnMissingPrecondition fname (show def)
                                                        return def
                                                post' <- case post of
                                                    Just x -> return x
                                                    Nothing -> do
                                                        let def = defaultPostcondition sp
                                                        logEvent $ WarnMissingPostcondition fname (show def)
                                                        return def
                                                return $ Map.insert fname (Specification params pre' post') mp

