{-# LANGUAGE ExistentialQuantification #-}

module Caper.DeductionFailure(
    module Caper.Utils.Failure,
    module Caper.DeductionFailure
) where

import Caper.Utils.Failure

import Caper.RegionTypes
import Caper.ProverStates

data DeductionFailure =
    forall s. (AssertionLenses s) => MissingRegionByType RTId [Expr VariableID] (ValueExpression VariableID) s
    | AbduceConditions [VariableID] [Condition VariableID]

instance Show DeductionFailure where
    show (MissingRegionByType tid exps ve _) = "MissingRegion: " ++ show tid ++ show exps ++ "(" ++ show ve ++ ")"
    show (AbduceConditions vs cs) = "AbduceConditions: " ++ show vs ++ ": " ++ show cs

instance AbductionFailure DeductionFailure where
    abduceConditions = AbduceConditions
    handleAbduceConditions hlr (AbduceConditions vs cs) = hlr vs cs
    handleAbduceConditions _ _ = Nothing
