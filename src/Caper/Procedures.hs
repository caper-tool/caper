module Caper.Procedures where

import qualified Data.Map as Map
import Data.Foldable
import Control.Lens

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
defaultPrecondition sp = AssrtPure sp $ ConstBAssrt sp False

defaultPostcondition :: SourcePos -> Assrt
defaultPostcondition sp = AssrtPure sp $ ConstBAssrt sp True

-- TODO: Somewhere we should check that procedures don't have multiple arguments of the same name 

declrsToProcedureSpecs :: (Monad m, MonadRaise m, MonadLogger m) =>
                [FunctionDeclr] -> m (Map.Map String Specification)
declrsToProcedureSpecs = foldlM declrSpec Map.empty
        where
            declrSpec mp fdec@(FunctionDeclr sp fname pre post params _) = contextualise fdec $
                                        case Map.lookup fname mp of
                                            (Just _) -> raise $ OverloadedProcedure fname
                                            Nothing -> do
                                                pre' <- case pre of
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

