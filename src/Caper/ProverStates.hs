{-# LANGUAGE TemplateHaskell #-}
module Caper.ProverStates where

import Control.Lens
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (intercalate)

import qualified Caper.TypingContext as TC
import Caper.ProverDatatypes
import Caper.Prover

-- |The 'Assumptions' data type represents a list of assumptions.
-- It also records all of the free variables in the context, possibly
-- with their types.
data Assumptions = Assumptions {
        -- |The type bindings for all free variables.
        _assmBindings :: BindingContext,
        -- |The list of assumptions.  Should be consistent
        -- with the types declared in the bindings.
        _assmAssumptions :: [Condition VariableID]
        }
makeLenses ''Assumptions

instance AssumptionLenses Assumptions where
        --theAssumptions = lens id (\x y -> y)
        bindings = assmBindings
        assumptions = assmAssumptions
        assumptionVars = to (TC.domain . _assmBindings)

instance Show Assumptions where
        show ass = "[" ++ show (ass ^. bindings) ++ "]\n" ++
                intercalate "\n" (map show (ass ^. assumptions)) 

{-
instance MonadState Assumptions m => MonadDebugState m where
    showState = liftM show get
-}

-- |The empty assumption context.
emptyAssumptions :: Assumptions
emptyAssumptions = Assumptions TC.empty []

data Assertions = Assertions {
        _assrAssumptions :: Assumptions,
        _assrEVars :: Set VariableID,
        _assrAssertions :: [Condition VariableID]
}
makeLenses ''Assertions

instance AssumptionLenses Assertions where
        --theAssumptions = assrAssumptions
        bindings = assrAssumptions . bindings
        assumptions = assrAssumptions . assumptions
        assumptionVars = to (\s -> Set.difference (TC.domain (s ^. assrAssumptions . bindings)) (_assrEVars s))

instance AssertionLenses Assertions where
        --theAssertions = lens id (\x y -> y)
        assertions = assrAssertions
        existentials = assrEVars

instance Show Assertions where
        show = showAssertions

emptyAssertions :: Assumptions -> Assertions
emptyAssertions asmts = Assertions asmts Set.empty []


data WithAssertions b = WithAssertions {
        _withAssrBase :: b,
        _withAssrEVars :: Set VariableID,
        _withAssrAssertions :: [Condition VariableID]
    }
makeLenses ''WithAssertions

instance AssumptionLenses b => AssumptionLenses (WithAssertions b) where
    -- theAssumptions = withAssrBase . theAssumptions
    bindings = withAssrBase . bindings
    assumptions = withAssrBase . assumptions
    assumptionVars = to (\s -> Set.difference (TC.domain (s ^. withAssrBase . bindings)) (_withAssrEVars s))

instance AssumptionLenses b => AssertionLenses (WithAssertions b) where
    assertions = withAssrAssertions 
    existentials = withAssrEVars

emptyWithAssertions :: (AssumptionLenses a) => a -> WithAssertions a
emptyWithAssertions x = WithAssertions x Set.empty []

-- | Admit all assertions as assumptions 
admitAssertions :: (AssumptionLenses a) => WithAssertions a -> a
admitAssertions asts = asts & _withAssrBase . (assumptions %~ (asts ^. assertions ++))  
