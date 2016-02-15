{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, MultiParamTypeClasses #-}
module Caper.DeclarationTyping (
        typeDeclarations
) where

import Prelude hiding (mapM_,foldl,elem)
import qualified Data.Map as Map
import Data.Map(Map)
import Data.Foldable
import Control.Monad.State hiding (mapM_)
import Data.List hiding (foldl,elem)
import Control.Lens.Indexed

-- import Debug.Trace

import Caper.Logger
import Caper.Parser.AST
import qualified Caper.TypingContext as TC
import Caper.ProverDatatypes
import Caper.Exceptions
import Caper.Utils.SimilarStrings

-- |List of free variables
freeL :: (FreeVariables t v, Eq v) => t -> [v]
freeL = foldrFree (:) []

-- |'TC.bind', but with a specilised type signature for Either
bindE :: (Ord v, Eq t) =>
        v -> t -> TC.TContext v t ->
        Either (TC.TypeUnificationException v t) (TC.TContext v t)
bindE = TC.bind

-- |Try to bind a variable to a type in a state context, possibly raising an
-- exception
bindR :: (Ord v, MonadState (TC.TContext v VariableType) m, MonadRaise m) =>
        v -> VariableType -> m ()
bindR key val = 
         get >>= liftTUMismatch . bindE key val >>= put

-- |'TC.unify', but specialised for Either
unifyE :: (Ord v, Eq t) => 
        v -> v -> TC.TContext v t -> 
        Either (TC.TypeUnificationException v t) (TC.TContext v t)
unifyE = TC.unify

-- |Try to unify the types of two variables in a state context, possibly
-- raising an exception.
unifyR :: (Ord v, MonadState (TC.TContext v VariableType) m, MonadRaise m) =>
        v -> v -> m ()
unifyR k1 k2 =
        get >>= liftTUMismatch . unifyE k1 k2 >>= put


{- |Determine the parameter typing for the given declarations.
   An exception can occur if the type is overspecified (i.e. a variable
   is used at inconsistent types).  If the type is underspecified, it defaults
   to Value, and a warning is logged.
-}
typeDeclarations :: (MonadLogger m, MonadRaise m) =>
        [Declr] -> m (Map String [(String, VariableType)])
typeDeclarations decs0 = do
                let decs = regionDeclrs decs0 
                let decCounts = foldl decCount Map.empty decs
                let tc0 = ifoldl initialDec TC.empty decCounts
                tc <- flip execStateT tc0 $
                                mapM_ (typeDeclaration decCounts) decs
                foldlM (tdm tc) Map.empty decs
        where
                decCount m (RegionDeclr _ rtname rparas _ _ _) =
                        Map.insert rtname (length rparas) m
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
                initialDec i m v =
                        (either undefined id . bindE (Left (i,0)) VTRegionID) $ 
                        TC.declareAll [Left (i, n) | n <- [0..v - 1]]
                                                m


typeDeclaration :: (MonadState (TC.TContext (Either (String,Int) String) VariableType) m,
        MonadRaise m) =>
        Map String Int ->
        RegionDeclr -> m ()
typeDeclaration decCounts dc@(RegionDeclr sp rtname rparas gdecs sis actions) =
          contextualise dc $ do
                mapM_ (typeStateInterp decCounts resVar Left) sis
                mapM_ (typeAction resVar) actions
        where
                resVar s = maybe (Right s) (\x -> Left (rtname, x))
                        (elemIndex s rparas) 

typeStateInterp :: (MonadState (TC.TContext a VariableType) m,
        MonadRaise m, Ord a)
        => Map String Int
        -> (String -> a)
        -> ((String, Int) -> a) 
        -> StateInterpretation
        -> m ()
typeStateInterp decCounts resVar resArg si = do
        s <- get
        mapM_ (typePureAssrt resVar) (siConditions si)
        mapM_ (typeVarExprAs VTValue resVar) (freeL (siState si))
        typeAssrt decCounts resVar resArg (siInterp si)
        modify (`TC.intersection` s)

typeAction :: (MonadState (TC.TContext a VariableType) m, 
        MonadRaise m, Ord a)
        => (String -> a)
        -> Action
        -> m ()
typeAction resVar (Action _ cnds grd pre post) = do
        s <- get
        mapM_ (typePureAssrt resVar) cnds
        mapM_ (typeGuard resVar) grd
        mapM_ (typeVarExprAs VTValue resVar) $ freeL
                [pre, post]
        modify (`TC.intersection` s)


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
                tpa (BinaryVarAssrt {}) = return ()
                tpa (BinaryValAssrt _ _ ve1 ve2) = mapM_ 
                        (typeVarExprAs VTValue resVar)
                        (freeL [ve1, ve2])
                tpa (BinaryPermAssrt _ _ pe1 pe2) = mapM_
                        (typeVarExprAs VTPermission resVar)
                        (freeL [pe1, pe2])

typeGuard :: forall a m. (MonadState (TC.TContext a VariableType) m,
        MonadRaise m, Ord a)
        => (String -> a)
        -> Guard
        -> m ()
typeGuard  resVar (NamedGuard _ _) = return ()
typeGuard resVar (PermGuard _ _ pe) = mapM_
        (typeVarExprAs VTPermission resVar) (freeL pe)
typeGuard resVar (ParamGuard _ _ args) = mapM_ (typeVarExprAs VTValue resVar) (freeL args)
typeGuard resVar (ParamSetGuard _ _ vs pas) = mapM_ (typeVarExprAs VTValue resVar) (filter notbnd $ freeL pas)
        where
          notbnd (Variable _ v) = not $ v `elem` vs
          notbnd _ = False -- might as well throw away wildcards immediately


typeAssrt :: forall a m. (MonadState (TC.TContext a VariableType) m,
        MonadRaise m, Ord a)
        => Map String Int
        -> (String -> a)
        -> ((String, Int) -> a)
        -> Assrt
        -> m ()
typeAssrt decCounts resVar resArg = ta
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
                                (freeL ve)
                        bindR arg VTValue
                tArg arg (AnyPerm pe) = do
                        mapM_ (typeVarExprAs VTPermission resVar)
                                (freeL pe)
                        bindR arg VTPermission
                ts (SARegion regass@(Region sp tname rid args st)) = do
                        contextualise regass $
                                case Map.lookup tname decCounts of
                                        Just c ->
                                            unless (c == length args + 1) $
                                                raise $ ArgumentCountMismatch 
                                                        (c + 1)
                                                        (length args + 2)
                                        Nothing -> raise $ UndeclaredRegionType
                                                tname (similarStrings tname 
                                                        (Map.keys decCounts))
                        addContext (DescriptiveContext sp $
                                        "In the first argument" ++
                                        " of a region assertion of type '" ++
                                        tname ++ "'") $
                            bindR (resVar rid) VTRegionID
                        iforM_ args $ \i a -> addContext
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
                                (freeL st)
                ts (SAPredicate pd) =
                        contextualise pd $ 
                                raise $ SyntaxNotImplemented "predicates"
                ts (SACell ca) =
                          contextualise ca $
                                mapM_ (typeVarExprAs VTValue resVar)
                                        (freeL ca)
                ts (SAGuards grds@(Guards _ _ gds)) = contextualise grds $
                        mapM_ (typeGuard resVar) gds
