{-# LANGUAGE FlexibleContexts, FlexibleInstances, ScopedTypeVariables, MultiParamTypeClasses #-}
module Caper.Assertions.Produce where

import           Control.Monad.State hiding (state)
import           Control.Monad.Reader
import           Control.Lens hiding (op)

import           Caper.Assertions.Check
import           Caper.Assertions.Generate
import           Caper.Exceptions
import qualified Caper.Guards as G
import           Caper.Parser.AST
import           Caper.Prover
import           Caper.ProverDatatypes
import           Caper.RegionTypes
import           Caper.Regions (RegionLenses)
import qualified Caper.Regions as R
import           Caper.SymbolicState (SymbStateLenses)
import qualified Caper.SymbolicState as SS
import           Caper.Utils.AliasingMap ()
import           Caper.Utils.NondetClasses
import Caper.Predicates (PredicateLenses)
import Caper.ProverStates

{-
        At some point, this whole module should probably be rewritten.
        In particular, some consideration of where variables are bound to
        types would be good.

        At present types are NOT bound by
                {produce,consume}{Value,Permission}Expr.
        This means that one should be careful to bind them correctly at point
        of use.
-}

class (MonadState s m, AssumptionLenses s, RegionLenses s, SymbStateLenses s,
        MonadReader r m, RTCGetter r, PredicateLenses r, DebugState s r,
        MonadRaise m, MonadDemonic m, MonadIO m, MonadLabel CapturedState m) => ProduceMonad r s m

instance (MonadState s m, AssumptionLenses s, RegionLenses s, SymbStateLenses s,
        MonadReader r m, RTCGetter r, PredicateLenses r, DebugState s r,
        MonadRaise m, MonadDemonic m, MonadIO m, MonadLabel CapturedState m) => ProduceMonad r s m        


-- |Given a syntactic pure assertion, produce it by adding it as an assumption.
producePure :: (MonadState s m, AssumptionLenses s, SymbStateLenses s,
        MonadRaise m) =>
                PureAssrt -> m ()
producePure assn = generatePure produceVariable assn >>= assumeE
{-
producePure = producePure' False
        where
                asm sp b = addSPContext sp . if b then assumeFalseE else assumeTrueE
                producePure' b (NotBAssrt _ pa) = producePure' (not $! b) pa
                producePure' b (ConstBAssrt _ b') = when (b == b') assumeContradiction
                producePure' b (BinaryVarAssrt sp ebo vl vr) = do  -- TODO: specialise handling
                                vvl <- produceVariable vl
                                vvr <- produceVariable vr
                                asm sp (b == (ebo == EqualRel))
                                        (EqualityCondition vvl vvr)
                producePure' b (BinaryValAssrt sp bo vel ver) = do
                                vvel <- produceValueExpr vel
                                vver <- produceValueExpr ver
                                asm sp b $
                                        valueRel bo vvel vver
                producePure' b (BinaryPermAssrt sp brel pel per) = do
                                let rel = permissionRel brel
                                ppel <- producePermissionExpr pel
                                pper <- producePermissionExpr per
                                asm sp b $ rel ppel pper
-}

-- |Produce a variable.  Named variables are converted to 'VIDNamed'
-- instances, and declared in the assumptions.  Anonymous (wildcard)
-- variables are translated to fresh identifiers.
produceVariable :: (MonadState s m, AssumptionLenses s, SymbStateLenses s) =>
                VarExpr -> m VariableID
produceVariable (Variable _ vname) = do
        v <- use (SS.logicalVars . at vname)
        case v of
                Nothing -> do
                        fv <- freshNamedVar vname
                        SS.logicalVars . at vname ?= fv
                        return fv
                (Just x) -> return x
produceVariable (WildCard _) =
                        newAvar "wildcard"


produceValueExpr :: (MonadState s m, AssumptionLenses s, SymbStateLenses s,
        MonadRaise m) =>
        ValExpr -> m (ValueExpression VariableID)
produceValueExpr = generateValueExpr produceVariable

producePermissionExpr :: (MonadState s m, AssumptionLenses s,
        SymbStateLenses s) =>
        PermExpr -> m (PermissionExpression VariableID)
producePermissionExpr = generatePermissionExpr produceVariable

produceAnyExpr :: (MonadState s m, AssumptionLenses s, SymbStateLenses s,
        MonadRaise m) =>
        AnyExpr -> m (Expr VariableID)
produceAnyExpr = generateAnyExpr produceVariable

produceCell :: ProduceMonad r s m =>
        CellAssrt -> m ()
produceCell p = generateCellPred produceVariable p >>= SS.producePredicate

-- |Produce a region assertion.
produceRegion :: ProduceMonad r s m =>
        Bool -- ^Should the region be treated as dirty (unstable)
        -> RegionAssrt -> m ()
produceRegion dirty regn@(Region sp rtn ridv lrps rse) = contextualise regn $
        do
                rtid <- lookupRTNameE rtn
                rid <- produceVariable (Variable sp ridv)
                addContext (StringContext $ "The region identifier '" ++ ridv ++ "'") $
                        bindVarAsE rid VTRegionID
                params <- mapM produceAnyExpr lrps
                checkRegionParams rtid (zip params lrps)
                state <- produceValueExpr rse
                bindVarsAsE state VTValue
                R.produceMergeRegion rid $ R.Region dirty (Just $ R.RegionInstance rtid params) (Just state) G.emptyGuard


-- |Produce a guard assertion.
-- If the guards are not compatible with a guard type for the region,
-- this will result in an assumption of inconsistency.  However, if the
-- guards are syntactically incompatible, an exception is raised instead.
produceGuards :: (ProduceMonad r s m) =>
        Guards -> m ()
produceGuards gg@(Guards sp ridv gds) = contextualise gg $
                do
                        rrid <- produceVariable (Variable sp ridv)
                        addContext (StringContext $ "The region identifier '" ++ ridv ++ "'") $
                                bindVarAsE rrid VTRegionID
                        guards <- generateGuard produceVariable assumeTrue gds
--                        guards <- liftM G.GD $ foldlM mkGuards Map.empty gds
                        R.produceMergeRegion rrid $
                                R.Region False Nothing Nothing guards
{-        where
            permExprHandler pe = assumeFalse $ PAEq pe PEZero
            permDisjHandler pe1 pe2 = assumeTrue $ PADis pe1 pe2 -}
{-        where
                mkGuards g gd@(NamedGuard _ nm) = contextualise gd $
                        if nm `Map.member` g then
                                raise $ IncompatibleGuardOccurrences nm
                        else
                                return $ Map.insert nm G.NoGP g
                mkGuards g gd@(PermGuard _ nm pe) = contextualise gd $ do
                        ppe <- producePermissionExpr pe
                        case Map.lookup nm g of
                                Nothing -> return $
                                        Map.insert nm (G.PermissionGP ppe) g
                                (Just (G.PermissionGP pe0)) -> return $
                                        Map.insert nm
                                                (G.PermissionGP (PESum pe0 ppe))
                                                g
                                _ -> raise $ IncompatibleGuardOccurrences nm
                mkGuards g gd@(ParamGuard _ nm es) = contextualise gd $
                        raise $ SyntaxNotImplemented "parametrised guards"
-}


producePredicate :: (ProduceMonad r s m) =>
        Predicate -> m ()
producePredicate pa = contextualise pa $
        generatePred produceVariable pa >>= SS.producePredicate

produceSpatial :: (ProduceMonad r s m) =>
        Bool ->
        SpatialAssrt -> m ()
produceSpatial dirty (SARegion a) = produceRegion dirty a
produceSpatial _ (SAPredicate a) = producePredicate a
produceSpatial _ (SACell a) = produceCell a
produceSpatial _ (SAGuards a) = produceGuards a

produceAssrt :: ProduceMonad r s m =>
        Bool ->
        Assrt -> m ()
produceAssrt _ (AssrtPure sp a) = producePure a
produceAssrt dirty (AssrtSpatial sp a) = produceSpatial dirty a
produceAssrt dirty (AssrtConj sp a1 a2) = produceAssrt dirty a1 >>
                                        produceAssrt dirty a2
produceAssrt dirty (AssrtITE sp c a1 a2) =
  (do
    label $ "case: " ++ show c
    producePure c 
    produceAssrt dirty a1) <#>
          (do
            label $ "case: " ++ show (NotBAssrt sp c)
            producePure (NotBAssrt sp c)
            produceAssrt dirty a2)
produceAssrt dirty (AssrtOr sp a1 a2) =
  (label ("left case: " ++ show a1) >> produceAssrt dirty a1)
  <#> (label ("right case: " ++ show a2) >> produceAssrt dirty a2)
