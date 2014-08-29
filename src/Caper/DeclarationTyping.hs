{-# LANGUAGE FlexibleContexts #-}
module Caper.DeclarationTyping where

import qualified Data.Map as Map
import Data.Map(Map)
import Control.Monad.State
import Data.List
import Control.Failure

import Caper.Parser.AST
import qualified Caper.TypingContext as TC
import Caper.ProverDatatypes
import Caper.Exceptions

typeDeclarations ::
        [Declr]
        -> (Map String [(String, VariableType)])
typeDeclarations decs =  undefined

typeDeclaration :: (MonadState (TC.TContext (Either (String,Int) String) VariableType) m) =>
        Declr -> m ()
typeDeclaration (RegionDeclr sp rtname rparas gdecs sis acts) = undefined
        where
                resVar s = maybe (Right s) (\x -> Left (rtname, x))
                        (elemIndex s rparas) 
typeDeclaration _ = return ()

typeStateInterp :: (MonadState (TC.TContext a VariableType) m) =>
        (String -> a)
        -> StateInterpretation
        -> m ()
typeStateInterp resVar si = undefined

typeVarExprAs :: (MonadState (TC.TContext a VariableType) m,
        MonadRaise m) =>
        VariableType
        -> (String -> a)
        -> VarExpr
        -> m ()
typeVarExprAs vt resVar (Variable _ v) = do
        s <- get
        case TC.bind (resVar v) vt s of
                (Left s') -> put s'
                (Right _) -> raise undefined 

