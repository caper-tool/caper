{-# LANGUAGE TemplateHaskell, MultiParamTypeClasses, FlexibleContexts, FlexibleInstances #-}
module Caper.ProverStates(
        module Caper.Prover,
        module Caper.ProverStates
) where

import Control.Lens
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List (intercalate)
import Control.Monad.Reader
import Control.Monad.State

import Caper.Utils.NondetClasses
import Caper.Utils.Failure

import qualified Caper.TypingContext as TC
import Caper.Logger
import Caper.Prover

class AbductionFailure f where
        abduceConditions :: [VariableID] -> [Condition VariableID] -> f
        handleAbduceConditions :: ([VariableID] -> [Condition VariableID] -> Maybe x) -> f -> Maybe x



showAssumptions :: (AssumptionLenses a) => a -> String
showAssumptions ass = "[" ++ show avars ++ "]\n" ++
                intercalate "\n" (map show (ass ^. assumptions))
            where
                avars = TC.filter (`Set.member` (ass ^. assumptionVars)) (ass ^. bindings)
                
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
        show = showAssumptions

{-
instance MonadState Assumptions m => MonadDebugState m where
    showState = liftM show get
-}

-- |The empty assumption context.
emptyAssumptions :: Assumptions
emptyAssumptions = Assumptions TC.empty []

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

-- |Admit the assumptions as assertions
admitChecks :: (MonadState s m, AssumptionLenses s) => StateT (WithAssertions s) m a -> m a
admitChecks o = do
                initial <- get
                (r, s') <- runStateT o (emptyWithAssertions initial)
                put $ admitAssertions s'
                return r

check :: (AssumptionLenses s, MonadLogger m, Provers p, MonadReader p m, OnFailure f m, AbductionFailure f, MonadOrElse m,
            MonadIO m, MonadState s m, MonadPlus m, DebugState (WithAssertions s) p, MonadLabel CapturedState m) =>
           StateT (WithAssertions s) m a -> m a
check c = admitChecks $ do
                r <- c
                labelS "Check assertions"
                justCheck'
                retry (return ()) $ (handleAbduceConditions handler)
                return r
        where
                handler vs cs = Just $ do
                        mapM_ declareEvar vs
                        mapM_ assert cs
                        labelS "Handling abduction"
                        justCheck'
                justCheck' = orElse (labelS "Checking assertions" >> justCheck) $ do
                        -- Check if the assertions are even possibly consistent with the assumptions
                        wasts <- get
                        consistent <- flip evalStateT (admitAssertions wasts) $ isConsistent
                        if consistent == Just True then
                                -- If they are, abduce
                                (failure =<< abduceConditions . Set.toList <$> use existentials <*> use assertions)
                            else
                                -- Otherwise there is no point
                                mzero

checkNoAbduce :: (AssumptionLenses s, MonadLogger m, Provers p, MonadReader p m,
            MonadIO m, MonadState s m, MonadPlus m, DebugState (WithAssertions s) p, MonadLabel CapturedState m) =>
           StateT (WithAssertions s) m a -> m a
checkNoAbduce c = admitChecks $ do
                r <- c
                labelS "Check assertions"
                justCheck
                return r



{-
type Assertions = WithAssertions Assumptions
emptyAssertions :: Assumptions -> Assertions
emptyAssertions = emptyWithAssertions
-}

class DebugState s r where
    showState :: r -> s -> String

instance DebugState Assumptions r where
        showState r = showAssumptions

instance DebugState (WithAssertions Assumptions) r where
        showState r = showAssertions

debugState :: (MonadState s m, MonadReader r m, DebugState s r, MonadIO m) => m ()
debugState = do
            r <- ask
            s <- get
            liftIO $ putStrLn $ showState r s

-- |PVarBindings map program variables (modelled as 'String's) to
-- expressions
type PVarBindings = Map String (ValueExpression VariableID)

-- |LVarBindings map syntactic logical variables ('String's) to their internal
-- representations ('VariableID's)
type LVarBindings = Map String VariableID

emptyLVars :: LVarBindings
emptyLVars = Map.empty

-- |A 'CapturedState' is a representation of the internal state
-- at a point in time.
newtype CapturedState = CapturedState String
instance Show CapturedState where
        show (CapturedState s) = s

captureState :: (MonadState s m, MonadReader r m, DebugState s r) => m CapturedState
captureState = do
        r <- ask
        s <- get
        return $ CapturedState $ showState r s

labelS :: (MonadState s m, MonadReader r m, DebugState s r, MonadLabel CapturedState m) =>
        String -> m ()
labelS l = do
        s <- captureState
        labelState s l
