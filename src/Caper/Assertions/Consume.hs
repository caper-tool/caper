{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, MultiParamTypeClasses, FlexibleInstances #-}
module Caper.Assertions.Consume where

import Control.Monad.State hiding (state)
import Control.Monad.Reader
import Control.Lens hiding (op)
import qualified Data.Set as Set

-- import Caper.Utils.Choice
import Caper.Utils.NondetClasses
import Caper.Utils.AliasingMap ()
import Caper.Logger
import Caper.Exceptions
import Caper.ProverDatatypes
import Caper.Prover
import Caper.ProverStates
import Caper.Parser.AST
import Caper.SymbolicState (SymbStateLenses)
import Caper.Predicates (PredicateLenses)
import qualified Caper.SymbolicState as SS
import Caper.Regions (RegionLenses)
import qualified Caper.Regions as R
import Caper.RegionTypes
import Caper.DeductionFailure
import qualified Caper.Guards as G
import Caper.Assertions.Generate
import Caper.Assertions.Check
-- import Caper.Assertions.Produce


class (MonadState s m, AssertionLenses s, RegionLenses s, SymbStateLenses s,
    MonadReader r m, RTCGetter r, PredicateLenses r, Provers r, DebugState s r,
    MonadRaise m, MonadLogger m, MonadPlus m, MonadOrElse m, Failure DeductionFailure m, MonadDemonic m,
    MonadIO m, MonadLabel m) => ConsumeMonad r s m

instance (MonadState s m, AssertionLenses s, RegionLenses s, SymbStateLenses s,
    MonadReader r m, RTCGetter r, PredicateLenses r, Provers r, DebugState s r,
    MonadRaise m, MonadLogger m, MonadPlus m, MonadOrElse m, Failure DeductionFailure m, MonadDemonic m,
    MonadIO m, MonadLabel m) => ConsumeMonad r s m

{-
        At some point, this whole module should probably be rewritten.
        In particular, some consideration of where variables are bound to
        types would be good.

        At present types are NOT bound by
                {produce,consume}{Value,Permission}Expr.
        This means that one should be careful to bind them correctly at point
        of use.
-}

consumeVariable :: (MonadState s m, AssertionLenses s, SymbStateLenses s) =>
                VarExpr -> m VariableID
consumeVariable (Variable _ vname) = do
        v <- use (SS.logicalVars . at vname)
        case v of
                Nothing -> do
                        fv <- freshNamedVar vname
                        declareEvar fv
                        SS.logicalVars . at vname ?= fv
                        return fv
                (Just x) -> return x
consumeVariable (WildCard _) =
                        newEvar "wildcard"

-- |Consume a variable as a region identifier.  This is a special case, because
-- we really want to choose from the existing identifiers.
--
-- XXX: This is probably only used for named variables (no wildcards) so
-- perhaps it would be wise to specialise it.
consumeRegionVariable :: (MonadState s m, AssertionLenses s, SymbStateLenses s,
        RegionLenses s, MonadPlus m, MonadRaise m, MonadLabel m) =>
                VarExpr -> m VariableID -> m VariableID
consumeRegionVariable (Variable _ vname) fallback = do
        v <- use (SS.logicalVars . at vname)
        case v of
                Nothing -> do
                        -- Choose a known region
                        rv <- (chooseFrom =<< R.regionList) `mplus` fallback
                        label $ "bind " ++ show vname ++ " as " ++ show rv
                        SS.logicalVars . at vname ?= rv
                        return rv
                Just x -> do
                        -- TODO: be cleverer here so that if it is not already
                        -- bound then we try to unify with known regions.
                        bindVarAsE x VTRegionID
                        return x
consumeRegionVariable (WildCard _) fallback = do
        rv <- (chooseFrom =<< R.regionList) `mplus` fallback
        label $ "bind region identifier as " ++ show rv
        return rv

consumeValueExpr :: (MonadState s m, AssertionLenses s, SymbStateLenses s,
        MonadRaise m) =>
        ValExpr -> m (ValueExpression VariableID)
consumeValueExpr = generateValueExpr consumeVariable

consumePermissionExpr :: (MonadState s m, AssertionLenses s,
        SymbStateLenses s) =>
        PermExpr -> m (PermissionExpression VariableID)
consumePermissionExpr = generatePermissionExpr consumeVariable

consumeAnyExpr :: (MonadState s m, AssertionLenses s, SymbStateLenses s,
        MonadRaise m) =>
        AnyExpr -> m (Expr VariableID)
consumeAnyExpr = generateAnyExpr consumeVariable

consumePure :: (MonadState s m, AssertionLenses s, SymbStateLenses s,
        MonadRaise m, MonadPlus m, MonadLogger m) =>
                PureAssrt -> m ()
consumePure assn = generatePure consumeVariable assn >>= assertE
{-
consumePure = consumePure' False
        where
                asrt sp b = addSPContext sp . if b then assertFalseE else assertTrueE
                consumePure' b (NotBAssrt _ pa) = consumePure' (not $! b) pa
                consumePure' b (ConstBAssrt _ b') = when (b == b') assertContradiction
                consumePure' b (BinaryVarAssrt sp ebo vl vr) = do  -- TODO: specialise handling
                        vvl <- consumeVariable vl
                        vvr <- consumeVariable vr
                        asrt sp (b == (ebo == EqualRel)) $
                                EqualityCondition vvl vvr
                consumePure' b (BinaryValAssrt sp bo vel ver) = do
                        let rel = valueRel bo
                        vvel <- consumeValueExpr vel
                        vver <- consumeValueExpr ver
                        asrt sp b $ rel vvel vver
                consumePure' b (BinaryPermAssrt sp brel pel per) = do
                        let rel = permissionRel brel
                        ppel <- consumePermissionExpr pel
                        pper <- consumePermissionExpr per
                        asrt sp b $ rel ppel pper
-}

consumeCell :: (MonadPlus m, MonadState s m, AssertionLenses s,
        SymbStateLenses s, MonadRaise m, MonadLogger m, MonadLabel m) =>
        CellAssrt -> m ()
-- Note: it shouldn't be necessary to check the number and type of arguments
-- after the call to generateCellPred.
consumeCell p = generateCellPred consumeVariable p >>= SS.consumePred

-- |Consume a region assertion.
consumeRegion :: (ConsumeMonad r s m) =>
        RegionAssrt -> m ()
consumeRegion regn@(Region sp rtn ridv lrps rse) = contextualise regn $
        do
                logEvent $ InfoEvent $ "Consuming region: " ++ show regn
                rtid <- lookupRTNameE rtn
                params <- mapM consumeAnyExpr lrps
                checkRegionParams rtid (zip params lrps)
                st <- consumeValueExpr rse
                bindVarsAsE st VTValue
                rid <- addContext
                        (StringContext $ "The region identifier '" ++ ridv ++ "'") $
                        consumeRegionVariable (Variable sp ridv)
                            (get >>= failure . MissingRegionByType rtid params st)
                logEvent $ InfoEvent $ "...: " ++ show rtid ++ ", " ++ show rid ++ show params ++ " " ++ show st
                R.consumeRegion rtid rid params st
                debugState 
                logEvent $ InfoEvent $ "Consumed region: " ++ show regn 

-- |Consume a guard assertion.
consumeGuards :: (ConsumeMonad r s m) =>
        Guards -> m ()
consumeGuards gg@(Guards sp ridv gds) = contextualise gg $
        do
                rid <- addContext (StringContext $ "The region identifier '" ++ ridv ++ "'") $
                        consumeRegionVariable (Variable sp ridv) mzero
                region <- liftMaybe =<< preuse (R.regions . ix rid) -- Backtracks if no such region
                consumeWith <- case R.regTypeInstance region of
                        Just ri -> liftM (G.consumeGuard . rtGuardType)
                                (lookupRType (R.riType ri))
                        Nothing -> return G.consumeGuardNoType
                let g0 = R.regGuards region
                let cw g gd = do
                        (nm, gp) <- guardToNameParam consumeVariable gd
                        case gp of
                            G.PermissionGP perm -> assertFalse $ PAEq perm PEZero
                            _ -> return ()
                        consumeWith nm gp g
                g1 <- foldM cw g0 gds
                R.regions . ix rid .= region {R.regDirty = True, R.regGuards = g1}

consumePredicate :: (ConsumeMonad r s m) =>
        Predicate -> m ()
consumePredicate pa = contextualise pa $
        generatePred consumeVariable pa >>= SS.consumePredicate

consumeSpatial :: (ConsumeMonad r s m) =>
        SpatialAssrt -> m ()
consumeSpatial (SARegion a) = consumeRegion a
consumeSpatial (SAPredicate a) = consumePredicate a
consumeSpatial (SACell a) = consumeCell a
consumeSpatial (SAGuards a) = consumeGuards a

consumeAssrt :: (ConsumeMonad r s m) =>
        Assrt -> m ()
consumeAssrt (AssrtPure sp a) = consumePure a
consumeAssrt (AssrtSpatial sp a) = consumeSpatial a
consumeAssrt (AssrtConj sp a1 a2) = consumeAssrt a1 >> consumeAssrt a2
consumeAssrt (AssrtITE sp c a1 a2) = {-
  ((do
    liftIO $ putStrLn $ "*** case " ++ show c
    producePure c
    succeedIfInconsistent
    consumeAssrt a1) <#>
        (do
            liftIO $ putStrLn $ "*** case " ++ show (NotBAssrt sp c)
            producePure (NotBAssrt sp c)
            succeedIfInconsistent
            consumeAssrt a2)) `mplus` -}
      (do
        label $ "assert case " ++ show c
        consumePure c
        consumeAssrt a1) `mplus`
      (do
        label $ "assert case " ++ show (NotBAssrt sp c)
        consumePure (NotBAssrt sp c)
        consumeAssrt a2) `mplus`
      (do
        a <- generatePure assumptionVariable c
        label $ "case split"
        (do
            label $ "case " ++ show c
            assumeE a
            consumeAssrt a1) <#>
          (do
            label $ "*** case " ++ show (NotBAssrt sp c)
            assumeFalseE a
            consumeAssrt a2))
  where
    assumptionVariable (Variable _ vname) = do
        v <- use (SS.logicalVars . at vname)
        case v of
            Nothing -> mzero
            (Just x) -> do
                    avs <- use assumptionVars
                    if Set.member x avs then return x else mzero
    assumptionVariable (WildCard _) = mzero
consumeAssrt (AssrtOr sp a1 a2) =
        (label ("left case: " ++ show a1) >> consumeAssrt a1)
        `mplus` (label ("right case: " ++ show a2) >> consumeAssrt a2)
