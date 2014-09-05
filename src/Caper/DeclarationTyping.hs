{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}
module Caper.DeclarationTyping (
        typeDeclarations
) where

import Prelude hiding (mapM_)
import qualified Data.Map as Map
import Data.Map(Map)
import Data.Foldable
import Control.Monad.State hiding (mapM_)
import Data.List
--import Control.Monad.Exception()
import Control.Lens.Indexed

import Caper.Logger
import Caper.Parser.AST
import qualified Caper.TypingContext as TC
import Caper.ProverDatatypes
import Caper.Exceptions


bindE :: (Ord v, Eq t) =>
        v -> t -> TC.TContext v t ->
        Either (TC.TypeUnificationException v t) (TC.TContext v t)
bindE = TC.bind

bindR :: (Ord v, MonadState (TC.TContext v VariableType) m, MonadRaise m) =>
        v -> VariableType -> m ()
bindR key val = get >>= liftTUMismatch . bindE key val >>= put

unifyE :: (Ord v, Eq t) => 
        v -> v -> TC.TContext v t -> 
        Either (TC.TypeUnificationException v t) (TC.TContext v t)
unifyE = TC.unify

unifyR :: (Ord v, MonadState (TC.TContext v VariableType) m, MonadRaise m) =>
        v -> v -> m ()
unifyR k1 k2 = get >>= liftTUMismatch . unifyE k1 k2 >>= put


{- |Determine the parameter typing for the given declarations.
   An exception can occur if the type is overspecified (i.e. a variable
   is used at inconsistent types).  If the type is underspecified, it defaults
   to Value, and a warning is logged.
   
-}
typeDeclarations :: (MonadLogger m, MonadRaise m) =>
        [Declr] -> m (Map String [(String, VariableType)])
typeDeclarations decs = do
                tc <- flip execStateT TC.empty $
                                mapM_ typeDeclaration decs
                foldlM (tdm tc) Map.empty decs
        where
                tdm tc m dc@(RegionDeclr _ rtname rparas _ _ _) = 
                    contextualise dc $ do
                        pts <- iforM rparas $ \i nm ->
                                case TC.lookup (Left (rtname, i)) tc of
                                    TC.JustType t -> return (nm, t)
                                    TC.Undetermined -> do
                                        logEvent $ WarnUnconstrainedParameter
                                                nm VTValue
                                        return (nm, VTValue) 
                                    _ -> error $ "typeDeclarations: parameter '"
                                        ++ nm ++ "' of region type '"
                                        ++ rtname ++ "' has no type."
                        return $ Map.insert rtname pts m
                tdm _ m _ = return m


typeDeclaration :: (MonadState (TC.TContext (Either (String,Int) String) VariableType) m,
        MonadRaise m) =>
        Declr -> m ()
typeDeclaration dc@(RegionDeclr sp rtname rparas gdecs sis actions) =
          contextualise dc $ do
                modify $ TC.declareAll [Left (rtname, n) |
                                n <- [0..length rparas - 1]]
                modify $ either undefined id . bindE (Left (rtname, 0))
                                VTRegionID
                mapM_ (typeStateInterp resVar) sis
                mapM_ (typeAction resVar) actions
        where
                resVar s = maybe (Right s) (\x -> Left (rtname, x))
                        (elemIndex s rparas) 
typeDeclaration _ = return ()

typeStateInterp :: (MonadState (TC.TContext a VariableType) m,
        MonadRaise m, Ord a)
        => (String -> a)
        -> StateInterpretation
        -> m ()
typeStateInterp resVar si = do
        s <- get
        mapM_ (typePureAssrt resVar) (siConditions si)
        mapM_ (typeVarExprAs VTValue resVar) (foldrFree (:) [] (siState si))
        typeAssrt resVar Left (siInterp si)
        modify (`TC.intersection` s)

typeAction :: (MonadState (TC.TContext a VariableType) m, 
        MonadRaise m, Ord a)
        => (String -> a)
        -> Action
        -> m ()
typeAction resVar action = do
        s <- get
        mapM_ (typePureAssrt resVar) (actionConditions action)
        mapM_ (typeVarExprAs VTValue resVar) $ foldrFree (:) []
                [actionPreState action, actionPostState action]
        modify (`TC.intersection` s)


type TCResult a b = Either (TC.TypeUnificationException a b)
                        (TC.TContext a b)

typeVarExprAs :: forall a m. (MonadState (TC.TContext a VariableType) m,
        MonadRaise m, Ord a) =>
        VariableType
        -> (String -> a)
        -> VarExpr
        -> m ()
typeVarExprAs vt resVar ve = contextualise ve $ tve ve
        where
        tve (Variable _ v) = bindR (resVar v) vt
        tve _ = return ()

typePureAssrt :: forall a m. (MonadState (TC.TContext a VariableType) m,
        MonadRaise m, Ord a)
        => (String -> a)
        -> PureAssrt
        -> m ()
typePureAssrt resVar = tpa
        where
                tpa (ConstBAssrt _ _) = return ()
                tpa (NotBAssrt _ pa) = tpa pa
                tpa a@(BinaryVarAssrt sp _ (Variable _ v1) (Variable _ v2)) =
                        addContext (DescriptiveContext sp $
                                "In the (dis)equality: '" ++ show a ++ "'") $
                                unifyR (resVar v1) (resVar v2)
                tpa (BinaryVarAssrt _ _ _ _) = return ()
                tpa (BinaryValAssrt _ _ ve1 ve2) = mapM_ 
                        (typeVarExprAs VTValue resVar)
                        (foldrFree (:) [] [ve1, ve2])
                tpa (BinaryPermAssrt _ _ pe1 pe2) = mapM_
                        (typeVarExprAs VTPermission resVar)
                        (foldrFree (:) [] [pe1, pe2])

typeAssrt :: forall a m. (MonadState (TC.TContext a VariableType) m,
        MonadRaise m, Ord a)
        => (String -> a)
        -> ((String, Int) -> a)
        -> Assrt
        -> m ()
typeAssrt resVar resArg = ta
        where
                ta (AssrtPure _ a) = typePureAssrt resVar a
                ta (AssrtSpatial _ a) = ts a
                ta (AssrtConj _ a1 a2) = ta a1 >> ta a2
                ta (AssrtITE _ ac a1 a2) = typePureAssrt resVar ac >> ta a1
                                        >> ta a2
                tArg arg (AnyVar ve@(Variable _ v)) = contextualise ve $ 
                        unifyR arg (resVar v)
                tArg _ (AnyVar _) = return ()
                tArg arg (AnyVal ve) = do
                        mapM_ (typeVarExprAs VTValue resVar)
                                (foldrFree (:) [] ve)
                        bindR arg VTValue
                tArg arg (AnyPerm pe) = do
                        mapM_ (typeVarExprAs VTPermission resVar)
                                (foldrFree (:) [] pe)
                        bindR arg VTPermission
                ts (SARegion (Region sp tname rid args st)) = do -- TODO: check the number of arguments!
                        
                        addContext (DescriptiveContext sp $
                                        "In the first argument" ++
                                        " of a region assertion of type '" ++
                                        tname ++ "'") $
                            bindR (resVar rid) VTRegionID
                        iforM args $ \i a -> addContext
                                (DescriptiveContext sp $
                                        "In argument " ++ show (i + 2) ++
                                        " of a region assertion of type '" ++
                                        tname ++ "'") $
                                tArg (resArg (tname, i + 1)) a 
                        addContext (DescriptiveContext sp $
                                        "In the last (state) argument" ++
                                        " of a region assertion of type '" ++
                                        tname ++ "'") $
                            mapM_ (typeVarExprAs VTValue resVar)
                                (foldrFree (:) [] st)