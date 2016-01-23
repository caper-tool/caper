{-# LANGUAGE MultiParamTypeClasses #-}
module Caper.RegionInterpretations where

import Prelude hiding (mapM_)
import Control.Monad.Reader hiding (mapM_,forM_)
import Control.Monad.State hiding (mapM_,forM_)
-- import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Lens
import Data.Foldable
import Data.Maybe

import Caper.Utils.Alternating
import Caper.Utils.Failure

import qualified Caper.Parser.AST.Annotation as AST
import Caper.Parser.AST.Annotation (StateInterpretation(..))
import Caper.ProverDatatypes
import Caper.RegionTypes
import Caper.Regions
import Caper.SymbolicState
import Caper.Exceptions
import Caper.Logger
import Caper.Prover
import Caper.ProverStates
import Caper.Assertions.Check
import Caper.Assertions.Produce
import Caper.Assertions.Consume
import Caper.Predicates

{--
-- Actually, this is probably part of the AST...
data StateInterpretation = StateInterpretation {
        siConditions :: [AST.PureAssrt],
        siState :: AST.ValExpr,
        siInterp :: AST.Assrt
        }
--} 
{-
siVariables :: StateInterpretation -> Set.Set (Maybe String)
siVariables si = Set.union (freeVariables (siConditions si))
                        (freeVariables (siState si))
-}

-- |Check if each state that matches the state interpretation is unambiguously
-- generated by a valuation of the variables.  This check is conservative.
checkStateInterpretationSelfAmbiguity ::
        (MonadRaise m, MonadIO m, MonadLogger m,
        MonadReader r m, Provers r) =>
        [String] -- ^The region parameters
        -> StateInterpretation
                -- ^The state interpretation to check for self-ambiguity
        -> m ()
checkStateInterpretationSelfAmbiguity params si@(StateInterpretation _ cs se _) =
                flip evalStateT (emptyWithAssertions emptySymbState) $ do
                        -- Produce the parameters
                        mapM_ produceVariable
                                [AST.Variable undefined x | x <- params]
                        savedVars <- use logicalVars
                        -- Produce the conditions once
                        mapM_ producePure cs
                        state1 <- produceValueExpr se
                        vars1 <- use logicalVars
                        logicalVars .= savedVars
                        -- Produce the conditions again, but with different
                        -- variables
                        mapM_ producePure cs
                        state2 <- produceValueExpr se
                        vars2 <- use logicalVars
                        -- Assume the states are equal
                        assumeTrueE $ VAEq state1 state2
                        -- Now assert that the variables are equal
                        forM_ (Map.toList vars1) $ \(vn, v1) -> do
                                let v2 = Map.findWithDefault
                                        (error $ "checkStateInterpretationSelfAmbiguity: no second binding for " ++ vn)
                                        vn vars2
                                assertTrueE $ EqualityCondition v1 v2
                        r <- checkAssertions
                        unless r $ raise OverlappingStateInterpretation

-- |Check that no state can match two (different) state interpretations. This
-- check is conservative.
checkStateInterpretationOtherAmbiguity ::
        (MonadRaise m, MonadIO m, MonadLogger m,
        MonadReader r m, Provers r) =>
        [String] -- ^The region parameters
        -> StateInterpretation
        -> StateInterpretation
        -> m ()
checkStateInterpretationOtherAmbiguity params si1 si2 =
        flip evalStateT emptySymbState $ do
                        -- Produce the parameters
                        mapM_ produceVariable
                                [AST.Variable undefined x | x <- params]
                        savedVars <- use logicalVars
                        -- Produce the first value
                        mapM_ producePure (siConditions si1)
                        state1 <- produceValueExpr (siState si1)
                        vars1 <- use logicalVars
                        logicalVars .= savedVars
                        -- Produce the second value
                        mapM_ producePure (siConditions si2)
                        state2 <- produceValueExpr (siState si2)
                        vars2 <- use logicalVars
                        -- Assume that the states are equal
                        assumeTrueE $ VAEq state1 state2
                        b <- isConsistent
                        unless (b == Just False) $ raise OverlappingStateInterpretation
                        
-- |Check that a list of state interpretations are unambiguous.  That is, there
-- is only one interpretation for each state.
checkStateInterpretations ::
        (MonadRaise m, MonadIO m, MonadLogger m,
        MonadReader r m, Provers r, RTCGetter r) =>
        [String] -- ^The region parameters
        -> [StateInterpretation]
        -> m ()
checkStateInterpretations _ [] = return ()
checkStateInterpretations params (si : sis) = do
                checkStateInterpretationStability params si
                checkStateInterpretationSelfAmbiguity params si
                mapM_ (checkStateInterpretationOtherAmbiguity params si) sis
                checkStateInterpretations params sis

-- |Check that a state interpretation is stable.
checkStateInterpretationStability ::
        (MonadRaise m, MonadIO m, MonadLogger m,
        MonadReader r m, Provers r, RTCGetter r) =>
        [String] -- ^The region parameters
        -> StateInterpretation
        -> m ()
checkStateInterpretationStability params si = 
    contextualise si $ unless (isTriviallyStable (siInterp si)) $ do
        r <- runAlternatingT $ flip evalStateT emptySymbState $ do
                -- Produce the abstract state
                state0 <- produceValueExpr (siState si)
                -- Assume the conditions
                forM_ (siConditions si) producePure
                -- Produce the concrete state
                produceAssrt True (siInterp si)
                -- Stabilise regions
                stabiliseRegions
                -- Clear the logical variables
                logicalVars .= emptyLVars
                check $ do 
                    -- Consume the new abstract state
                    state1 <- consumeValueExpr (siState si)
                    -- Assert that the state is the same
                    assertEqual state0 state1
                    -- Assert the conditions
                    forM_ (siConditions si) consumePure
                    debugState
                    -- Consume the concrete state
                    consumeAssrt (siInterp si)
                    debugState
                    use logicalVars >>= liftIO . putStrLn . show
        when (isNothing r) $
            raise UnstableStateInterpretation

checkRegionType :: 
        (MonadRaise m, MonadIO m, MonadLogger m,
        MonadReader r m, Provers r, RTCGetter r) =>
        RegionType -> m ()
checkRegionType rt = contextualise rt $ checkStateInterpretations (rtParamNames rt)
                        (rtInterpretation rt)
                
checkRegionTypeContextInterpretations ::
        (MonadRaise m, MonadIO m, MonadLogger m,
        MonadReader r m, Provers r, RTCGetter r) =>
        m ()
checkRegionTypeContextInterpretations = 
        view theRTContext >>= mapM_ checkRegionType . rtcRegionTypes
