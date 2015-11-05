{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE BangPatterns #-}
module Caper.Prover(
        -- * Assumptions
        --Assumptions,
        BindingContext,
        AssumptionLenses(..),
        --emptyAssumptions,
        ProverM,
        -- ** Variable type bindings
        boundVars,
        isBound,
        bindVarsAs,
        bindVarsAsE,
        bindVarAs,
        bindVarAsE,
        checkExpressionAtType,
        checkExpressionAtTypeE,
        --unifyEqVars,
        --unifyEqVarsE
        -- ** Adding assumptions
        assume,
        assumeContradiction,
        assumeTrue,
        assumeFalse,
        -- ** Adding assumptions (raising exceptions)
        assumeE,
        assumeTrueE,
        assumeFalseE,
        -- ** Consistency
        isConsistent,
        -- * Assertions
        --Assertions,
        AssertionLenses(..),
        --emptyAssertions,
        --WithAssertions,
        --withAssrBase,
        --emptyWithAssertions,
        -- ** Display
        showAssertions,
        printAssertions,
        -- ** Adding assertions
        assert,
        assertContradiction,
        assertEqual,
        assertTrue,
        assertFalse,
        assertEqualE,
        assertTrueE,
        assertFalseE,
        -- ** Checking assertions
        checkAssertions,
        justCheck,
        hypothetical,
        --hypotheticalCheck,
        --admitAssertions, -- Questionable
        {- -- ** Variable type bindings
        universalBindings,
        existentialBindings -}
        -- * Checking first-order formulae
        valueCheck,
        permissionCheck,
        -- * Variables
        freshInternal,
        freshInternals,
        newAvar,
        declareVar,
        declareVars,
        declareEvar,
        newEvar,
        freshNamedVar,
        letAvar
        ) where
import Prelude hiding (sequence,foldl,foldr,mapM_,mapM,elem,notElem,any,all)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.State hiding (mapM_,mapM)
import Control.Monad.Reader
import Control.Monad.RWS
import Control.Monad.Trans.Maybe
import Control.Monad.Exception
import Control.Applicative
import Data.Maybe
import Data.Foldable
--import Data.Traversable
--import Data.Typeable
--import Control.Monad hiding (mapM_,mapM)
import Control.Lens
import Data.List (intercalate)

import Caper.ProverDatatypes
--import Caper.ValueProver
import qualified Caper.TypingContext as TC
--import Caper.FirstOrder
import Caper.Exceptions
import Caper.Logger


-- |A 'BindingContext' associates variables with their types (if determined).
type BindingContext = TC.TContext VariableID VariableType

{-
class DebugState s where
    showState :: s -> String

debugState :: (MonadIO m, DebugState r s, MonadReader r, Monad) => m ()
debugState = showState >>= liftIO . putStrLn
-}

{- TODO: tag assumptions with a 'corollary' flag to indicate
 - if it is a consequence of other assumptions.  Some types
 - of prover may work better without corollaries.  For instance,
 - the internal permissions prover will most likely waste time
 - with corollaries.
 -}


-- |'AssumptionLenses' is the typeclass for assumption state information.
-- An assumption state must provide a type binding for variables and
-- a list of conditions that are the assumptions.
class AssumptionLenses a where
        bindings :: Simple Lens a BindingContext
        assumptions :: Simple Lens a [Condition VariableID]
        assumptionVars :: Getter a (Set VariableID)


-- |A convenience type class synonym.
class (MonadIO m, MonadState s m, AssumptionLenses s, MonadReader r m, Provers r, MonadLogger m) => ProverM s r m
instance (MonadIO m, MonadState s m, AssumptionLenses s, MonadReader r m, Provers r, MonadLogger m) => ProverM s r m


boundVars :: (AssumptionLenses a) => Getter a (Set VariableID)
boundVars = to $ Set.fromDistinctAscList . map fst . Map.toAscList . TC.toMap . (^.bindings)



bindVarsAs :: (MonadState s m, AssumptionLenses s, Foldable f) => f VariableID -> VariableType -> m ()
bindVarsAs s vt = do
                        b0 <- use bindings
                        let !bs = case TC.bindAll s vt b0 of
                                (Left e) -> error (show (e :: TUException))
                                (Right r) -> r
                        bindings .= bs

bindVarsAsE :: (MonadState s m, AssumptionLenses s, Foldable f,
                MonadRaise m) =>
                f VariableID -> VariableType -> m ()
bindVarsAsE s vt = do
                        b0 <- use bindings
                        bs <- liftTUFailure $ TC.bindAll s vt b0
                        bindings .= bs

bindVarAs :: (MonadState s m, AssumptionLenses s) => VariableID -> VariableType -> m ()
bindVarAs = bindVarsAs . Identity

bindVarAsE :: (MonadState s m, AssumptionLenses s, MonadRaise m) => VariableID -> VariableType -> m ()
bindVarAsE = bindVarsAsE . Identity


unifyEqVars :: (MonadState s m, AssumptionLenses s) => VariableID -> VariableID -> m ()
unifyEqVars v1 v2 = do
                        b0 <- use bindings
                        bs <- runEMT $ TC.unify v1 v2 b0 `catch` (\(e :: TUException) -> error (show e))
                        bindings .= bs

unifyEqVarsE :: (MonadState s m, AssumptionLenses s, MonadRaise m) =>
                VariableID -> VariableID -> m ()
unifyEqVarsE v1 v2 = do
                        b0 <- use bindings
                        bs <- liftTUFailure $ TC.unify v1 v2 b0
                        bindings .= bs

declareVar :: (MonadState s m, AssumptionLenses s) => VariableID -> m ()
declareVar v = bindings %= TC.declare v

declareVars :: (MonadState s m, AssumptionLenses s, Foldable f) => f VariableID -> m ()
declareVars s = bindings %= TC.declareAll s


checkExpressionAtType :: (MonadState s m, AssumptionLenses s) => Expr VariableID -> VariableType -> m ()
-- ^Check that the expression is of the appropriate type,
-- binding the variables to be sure they are not inconsistently used.

-- First two cases are straightforward
checkExpressionAtType (PermissionExpr c) VTValue = error $ "A value expression was expected, but '" ++ show c ++ "' is a permission expression."
checkExpressionAtType (ValueExpr c) VTPermission = error $ "A permission expression was expected, but '" ++ show c ++ "' is a value expression."
checkExpressionAtType (PermissionExpr c) VTRegionID = error $ "A region identifier was expected, but '" ++ show c ++ "' is a permission expression."
checkExpressionAtType (ValueExpr c) VTRegionID = error $ "A region identifier was expected, but '" ++ show c ++ "' is a value expression."
checkExpressionAtType e VTValue = bindVarsAs (freeVariables e) VTValue
checkExpressionAtType e VTPermission = bindVarsAs (freeVariables e) VTPermission
checkExpressionAtType e VTRegionID = bindVarsAs (freeVariables e) VTRegionID

exprType :: Expr v -> Maybe VariableType
exprType (PermissionExpr _) = Just VTPermission
exprType (ValueExpr _) = Just VTValue
exprType _ = Nothing

-- |Check that the expression is of the appropriate type,
-- binding the variables to be sure that they are not inconsistently
-- used.  Raises an exception if the type cannot be made to match.
checkExpressionAtTypeE :: (MonadState s m, AssumptionLenses s, MonadRaise m) =>
        Expr VariableID -> VariableType -> m ()
checkExpressionAtTypeE e t = case exprType e of
                (Just t') -> if t == t' then
                                bindVarsAsE (freeVariables e) t
                        else
                                raise $ TypeMismatch t t'
                _ -> bindVarsAsE e t

isBound :: (MonadState s m, AssumptionLenses s) => VariableID -> m Bool
-- ^Determine if the given variable is bound.
isBound v = do
                b <- use bindings
                return $ TC.lookup v b /= TC.NotBound


-- Only use internally
addAssumption :: (MonadState s m, AssumptionLenses s) => Condition VariableID -> m ()
addAssumption c = assumptions %= (c :)

assume :: (MonadState s m, AssumptionLenses s) => Condition VariableID -> m ()
-- ^Add a condition to the list of assumptions, binding its
-- variables at the appropriate type.  This can raise an
-- error if a variable is not used with a consistent type.
assume c@(PermissionCondition pss) = do
                        bindVarsAs (freeVariables c) VTPermission
                        addAssumption c
assume c@(ValueCondition cass) = do
                        bindVarsAs (freeVariables c) VTValue
                        addAssumption c
assume c@(EqualityCondition v1 v2) = do
                        unifyEqVars v1 v2
                        addAssumption c
assume c@(DisequalityCondition v1 v2) = do
                        unifyEqVars v1 v2
                        addAssumption c

-- TODO: make this succeed faster
-- |Assume a contradiction.
assumeContradiction :: (MonadState s m, AssumptionLenses s) => m ()
assumeContradiction = assume condFalse

-- |Assume a condition to be true.
assumeTrue :: (ConditionProp c, MonadState s m, AssumptionLenses s) => c VariableID -> m ()
assumeTrue = assume . toCondition

-- |Assume a condition to be false.
assumeFalse :: (ConditionProp c, MonadState s m, AssumptionLenses s) => c VariableID -> m ()
assumeFalse = assume . negativeCondition

assumeE :: (MonadState s m, AssumptionLenses s, MonadRaise m) =>
                Condition VariableID -> m ()
-- ^Add a condition to the list of assumptions, binding its
-- variables at the appropriate type.  This can raise an
-- exception if a variable is not used with a consistent type.
assumeE c@(PermissionCondition pss) = do
                        bindVarsAsE (freeVariables c) VTPermission
                        addAssumption c
assumeE c@(ValueCondition cass) = do
                        bindVarsAsE (freeVariables c) VTValue
                        addAssumption c
assumeE c@(EqualityCondition v1 v2) = do
                        unifyEqVarsE v1 v2
                        addAssumption c
assumeE c@(DisequalityCondition v1 v2) = do
                        unifyEqVarsE v1 v2
                        addAssumption c

-- |Assume a condition to be true.  May raise an exception.
assumeTrueE :: (ConditionProp c, MonadState s m, AssumptionLenses s, MonadRaise m) =>
                c VariableID -> m ()
assumeTrueE = assumeE . toCondition
-- |Assume a condition to be false.  May raise an exception.
assumeFalseE :: (ConditionProp c, MonadState s m, AssumptionLenses s, MonadRaise m) =>
                c VariableID -> m ()
assumeFalseE = assumeE . negativeCondition

permissionConditions :: (Ord v) => TC.TContext v VariableType -> [Condition v] -> [FOF PermissionAtomic v]
permissionConditions tc [] = []
permissionConditions tc (PermissionCondition pa : xs) = pa : permissionConditions tc xs
permissionConditions tc (EqualityCondition v1 v2 : xs) = if TC.lookup v1 tc == TC.JustType VTPermission then (FOFAtom $ PAEq (PEVar v1) (PEVar v2)) : permissionConditions tc xs else permissionConditions tc xs
permissionConditions tc (DisequalityCondition v1 v2 : xs) = if TC.lookup v1 tc == TC.JustType VTPermission then (FOFNot $ FOFAtom $ PAEq (PEVar v1) (PEVar v2)) : permissionConditions tc xs else permissionConditions tc xs
permissionConditions tc (_ : xs) = permissionConditions tc xs


permissionAssumptions :: (AssumptionLenses a) => a -> [FOF PermissionAtomic VariableID]
-- ^Extract the assumptions pertaining to permissions
permissionAssumptions ass = permissionConditions (ass ^. bindings) (ass ^. assumptions)

permissionVariables :: (AssumptionLenses a) => a -> [VariableID]
-- ^Return a list of the permission variables
permissionVariables = Map.keys . Map.filter (== Just VTPermission) . TC.toMap . (^. bindings)

-- For passing to the prover, we will treat values and region identifiers, as well as
-- variables of indeterminate type, as values.
treatAsValueJ :: Maybe VariableType -> Bool
treatAsValueJ (Just VTValue) = True
treatAsValueJ (Just VTRegionID) = True
treatAsValueJ (Just VTPermission) = False
treatAsValueJ Nothing = True

treatAsValueJT :: TC.TypeResult VariableType -> Bool
treatAsValueJT (TC.JustType t) = treatAsValueJ (Just t)
treatAsValueJT TC.Undetermined = treatAsValueJ Nothing
treatAsValueJT _ = False

valueConditions :: (Ord v) => TC.TContext v VariableType -> [Condition v] -> [FOF ValueAtomic v]
valueConditions tc [] = []
valueConditions tc (EqualityCondition v1 v2 : xs) =
                if treatAsValueJT (TC.lookup v1 tc) then
                        (FOFAtom $ VAEq (var v1) (var v2)) : valueConditions tc xs
                else
                        valueConditions tc xs
valueConditions tc (DisequalityCondition v1 v2 : xs) =
                if treatAsValueJT (TC.lookup v1 tc) then
                        (FOFNot $ FOFAtom $ VAEq (var v1) (var v2)) : valueConditions tc xs
                else
                        valueConditions tc xs
valueConditions tc (ValueCondition cass : xs) = cass : valueConditions tc xs
valueConditions tc (_ : xs) = valueConditions tc xs

valueAssumptions :: (AssumptionLenses a) => a -> [FOF ValueAtomic VariableID]
-- ^Extract the assumptions pertaining to values (integers).
-- Equality assumptions where the variable type is indeterminate are treated as value assumptions.
valueAssumptions ass = valueConditions (ass ^. bindings) (ass ^. assumptions)

valueVariables :: (AssumptionLenses a) => a -> [VariableID]
-- ^Return a list of value variables; variables with no other type are treated as value variables.
valueVariables = Map.keys . Map.filter treatAsValueJ . TC.toMap . (^. bindings)

checkConsistency :: (Functor a, Foldable a, Show (a String)) => (FOF a String -> IO (Maybe Bool)) -> [VariableID] -> [FOF a VariableID] -> IO (Maybe Bool)
-- ^Given a first-order prover, check whether a list of assertions (with free variables from a given list) is consistent.
-- Consistent if the formula ¬(E) x1, ..., xn . P1 /\ ... /\ Pm /\ True is invalid. 
checkConsistency p vars asss = do
                        rp <- p $ FOFNot (varToString <$> foldr FOFExists (foldr FOFAnd FOFTrue asss) vars)
                        return $ fmap not rp

isConsistent :: ProverM s r m => m (Maybe Bool)
-- ^Check whether the current set of assumptions is consistent
-- (i.e. False does not follow).
isConsistent = do
                ps <- ask
                ass <- get
                liftIO $ do
                        rp <- checkConsistency (permissionsProver ps) (permissionVariables ass) (permissionAssumptions ass)
                        if rp == Just False then return $ Just False
                            else do
                                rv <- checkConsistency (valueProver ps) (valueVariables ass) (valueAssumptions ass)
                                return $ case (rp, rv) of
                                        (_, Just False) -> Just False
                                        (Just True, Just True) -> Just True
                                        _ -> Nothing


assumptionContext :: (Functor a, Foldable a) =>
        [v] -> [FOF a v] -> FOF a v -> FOF a v
-- ^Wrap universal quantifiers and assumptions around an assertion.
assumptionContext vids asms ast = foldr FOFForAll (foldr FOFImpl ast asms) vids


{-
 - So I was thinking of effectively binding existential variables
 - to values and doing substitutions with these.  This may have
 - the benefit of reducing the number of variables that are introduced.
 - However it would probably be better to implement solver simplifiers
 - that eliminate extraneous variables.  (Something to do later, when
 - performance goes to hell.)
 - Instead, you'll just have to introduce existential variables and
 - make assertions about them being equal to things.
 -}



{-
  TODO: Track in assertions when we have already checked provability.  This
        should not mess things up too much -- the lenses can be integrated
        so that they automatically set a dirty flag when it is updated.
        Something similar would be valuable for the consistency of assumptions,
        probably.
-}

-- AssertionLenses

class (AssumptionLenses a) => AssertionLenses a where
        assertions :: Simple Lens a [Condition VariableID]
        existentials :: Simple Lens a (Set VariableID)

universalBindings :: (AssertionLenses a) => Getter a BindingContext
universalBindings = to $ \s -> TC.filter (flip Set.notMember $ s ^. existentials) (s ^. bindings)

existentialBindings :: (AssertionLenses a) => Getter a BindingContext
existentialBindings = to $ \s -> TC.filter (flip Set.member $ s ^. existentials) (s ^. bindings)




showAssertions :: (AssertionLenses a) => a -> String
showAssertions asts = "Assumptions: !["
                ++ show (asts ^. universalBindings)
                ++ "] \n"
                ++ intercalate "\n" (map show (asts ^. assumptions))
                ++ "\nAssertions: ?["
                ++ show (asts ^. existentialBindings)
                ++ "] \n"
                ++ intercalate "\n" (map show (asts ^. assertions))

printAssertions :: (MonadIO m, MonadState s m, AssertionLenses s) => m ()
printAssertions = get >>= liftIO . putStrLn . showAssertions

bindAtExprType :: VariableID -> Expr VariableID -> BindingContext -> BindingContext
bindAtExprType v (PermissionExpr _) c = runEM $ TC.bind v VTPermission c `catch` (\(e :: TUException) -> error (show e))
bindAtExprType v (ValueExpr _) c = runEM $ TC.bind v VTValue c `catch` (\(e :: TUException) -> error (show e))
bindAtExprType v (VariableExpr v') c = runEM $ TC.unify v v' c `catch` (\(e :: TUException) -> error (show e))


suffices :: [String]
suffices = "" : map show [0::Int ..]

freshInternal :: (MonadState s m, AssumptionLenses s) => String -> m VariableID
-- ^Generate a variable that is not currently bound.
-- This DOES NOT create a variable binding, and so should only be used
-- when the binding will be generated by another mechanism, e.g. if it
-- is quantified within an assertion.
freshInternal vname = do
                vt <- use bindings
                return $ TC.firstFresh [ VIDInternal $ vname ++ suffix | suffix <- suffices ] vt

freshInternals :: (MonadState s m, AssumptionLenses s, Ord a) =>
        (a -> String) -> Set a -> m (Map.Map a VariableID)
freshInternals sify s = do
                ctx <- use bindings
                return $ fst $ foldr accum (Map.empty, ctx) s
        where
                accum vv (mp, cx)
                        | vv `Map.member` mp = (mp, cx)
                        | otherwise = let fvv = TC.firstFresh [ VIDInternal $ sify vv ++ suffix | suffix <- suffices ] cx in
                                (Map.insert vv fvv mp, TC.declare fvv cx)


-- |Make sure that a variable is bound and being treated as an 
-- assertion (i.e. existential) variable.
declareEvar :: (MonadState s m, AssertionLenses s) => VariableID -> m ()
declareEvar ev = do
                bindings %= TC.declare ev
                existentials %= Set.insert ev

newEvar :: (MonadState s m, AssertionLenses s) => String -> m VariableID
-- ^Generate a new assertion variable with a name like the one given
--
-- /WARNING/: No other mechanism should generate VIDExistential variables.
newEvar vname = do
                vt <- use bindings
                let evin = TC.firstFresh [ VIDExistential $ vname ++ suffix | suffix <- suffices ] vt
                declareEvar evin
                return evin

newAvar :: (MonadState s m, AssumptionLenses s) => String -> m VariableID
-- ^Generate a new assumption variable with a name like the one given
newAvar vname = do
                vt <- use bindings
                let avin = TC.firstFresh [ VIDInternal $ vname ++ suffix | suffix <- suffices ] vt
                bindings %= TC.declare avin
                return avin

areAvars :: (MonadState s m, AssumptionLenses s, Foldable f) => f VariableID -> m Bool
areAvars e = do
                avrs <- use assumptionVars
                return (all (`Set.member` avrs) e)

-- |Bind an assumption variable to an expression.
-- The expression must only contain assumption variables.
-- If the expression is just a variable, then that is used.
letAvar :: (MonadState s m, AssumptionLenses s) => String -> Expr VariableID -> m VariableID
letAvar vname e = do
                chk <- areAvars e
                unless chk $ error $ "letAVar: the expression '" ++ show e ++ "' contains non-assumption variables."
                letAvar' e
    where
        letAvar' (VariableExpr v) = return v
        letAvar' (ValueExpr (VEVar v)) = return v -- XXX: Possibly assert the type of v
        letAvar' (ValueExpr ve) = do
                    v <- newAvar vname
                    assume $ ValueCondition $ FOFAtom $ VAEq (var v) ve
                    return v
        letAvar' (PermissionExpr (PEVar v)) = return v
        letAvar' (PermissionExpr pe) = do
                    v <- newAvar vname
                    assume $ PermissionCondition $ FOFAtom $ PAEq (var v) pe
                    return v
                 

freshNamedVar :: (MonadState s m, AssumptionLenses s) => String -> m VariableID
-- ^Generate a fresh named variable with a name similar to the one given.
-- The variable is added to the binding context.
freshNamedVar vname = do
                vt <- use bindings
                let v = TC.firstFresh
                        [ VIDNamed $ vname ++ suffix | suffix <- suffices ] vt
                bindings %= TC.declare v
                return v

autoExists :: (MonadState s m, MonadLogger m, AssertionLenses s, Foldable f) =>
                f VariableID -> m ()
autoExists s = do
                b0 <- use boundVars
                let newvars = Set.difference ((Set.fromList . toList) s) b0
                unless (Set.null newvars) $ do
                        logEvent $ WarnAutoBind newvars
                        existentials %= flip Set.union newvars
                 

eBindVarsAs :: (MonadState s m, MonadLogger m, AssertionLenses s, Foldable f) =>
                f VariableID -> VariableType -> m ()
eBindVarsAs s vt = autoExists s >> bindVarsAs s vt

eUnifyEqVars :: (MonadState s m, MonadLogger m, AssertionLenses s) =>
                VariableID -> VariableID -> m ()
eUnifyEqVars v1 v2 = autoExists [v1, v2] >> unifyEqVars v1 v2

eBindVarsAsE :: (MonadState s m, MonadLogger m, MonadRaise m,
                AssertionLenses s, Foldable f) =>
                f VariableID -> VariableType -> m ()
eBindVarsAsE s vt = autoExists s >> bindVarsAsE s vt

eUnifyEqVarsE :: (MonadState s m, MonadLogger m, MonadRaise m,
                AssertionLenses s) =>
                VariableID -> VariableID -> m ()
eUnifyEqVarsE v1 v2 = autoExists [v1, v2] >> unifyEqVarsE v1 v2


assert :: (MonadState s m, MonadLogger m, AssertionLenses s) =>
        Condition VariableID -> m ()
-- ^Assert that a given condition holds.
-- We assume that all of the variables are already bound correctly
assert c@(PermissionCondition _) = do
                        eBindVarsAs (freeVariables c) VTPermission
                        assertions %= (c :)
assert c@(ValueCondition _) = do
                        eBindVarsAs (freeVariables c) VTValue
                        assertions %= (c :)
assert c@(EqualityCondition v1 v2) = do
                        eUnifyEqVars v1 v2
                        assertions %= (c :)
assert c@(DisequalityCondition v1 v2) = do
                        eUnifyEqVars v1 v2
                        assertions %= (c :)

assertE :: (MonadState s m, MonadLogger m, MonadRaise m, AssertionLenses s) =>
        Condition VariableID -> m ()
-- ^Assert that a given condition holds.
-- We assume that all of the variables are already bound correctly.
-- This version raises an exception if types of variables do not match.
assertE c@(PermissionCondition _) = do
                        eBindVarsAsE (freeVariables c) VTPermission
                        assertions %= (c :)
assertE c@(ValueCondition _) = do
                        eBindVarsAsE (freeVariables c) VTValue
                        assertions %= (c :)
assertE c@(EqualityCondition v1 v2) = do
                        eUnifyEqVarsE v1 v2
                        assertions %= (c :)
assertE c@(DisequalityCondition v1 v2) = do
                        eUnifyEqVarsE v1 v2
                        assertions %= (c :)


-- |Assert that two expressions are equal.
assertEqual :: (ProverExpression e, MonadState s m, AssertionLenses s,
        MonadLogger m) => e VariableID -> e VariableID -> m ()
assertEqual e1 e2 = assert $ exprEquality (toExpr e1) (toExpr e2)

-- |Assert that two expressions are equal.  Raises an exception if the variables
-- do not have appropriate types.
assertEqualE :: (ProverExpression e, MonadState s m, AssertionLenses s,
        MonadLogger m, MonadRaise m) => e VariableID -> e VariableID -> m ()
assertEqualE e1 e2 = assertE $ exprEquality (toExpr e1) (toExpr e2)

-- |Assert that a condition is true.
assertTrue :: (ConditionProp c, MonadState s m, AssertionLenses s,
        MonadLogger m) => c VariableID -> m ()
assertTrue = assert . toCondition

-- |Assert that a condition is false.
assertFalse :: (ConditionProp c, MonadState s m, AssertionLenses s,
        MonadLogger m) => c VariableID -> m ()
assertFalse = assert . negativeCondition

-- |Assert that a condition is true.
assertTrueE :: (ConditionProp c, MonadState s m, AssertionLenses s,
        MonadLogger m, MonadRaise m) => c VariableID -> m ()
assertTrueE = assertE . toCondition

-- |Assert that a condition is false.
assertFalseE :: (ConditionProp c, MonadState s m, AssertionLenses s,
        MonadLogger m, MonadRaise m) => c VariableID -> m ()
assertFalseE = assertE . negativeCondition


-- |Assert a contradiction.
assertContradiction :: (MonadState s m, AssertionLenses s, MonadLogger m) =>
        m ()
assertContradiction = assert condFalse

filterEvars :: (AssertionLenses a) => (Maybe VariableType -> Bool) -> Getter a [VariableID]
filterEvars f = to $ Map.keys . Map.filter f . TC.toMap . (^.existentialBindings)

permissionEvars :: (AssertionLenses a) => Getter a [VariableID]
permissionEvars = filterEvars (== Just VTPermission)
valueEvars :: (AssertionLenses a) => Getter a [VariableID]
valueEvars = filterEvars treatAsValueJ --(\x -> (x == Just VTValue) || isNothing x)

filterAvars :: (AssertionLenses a) => (Maybe VariableType -> Bool) -> Getter a [VariableID]
filterAvars f = to $ Map.keys . Map.filter f . TC.toMap . (^.universalBindings)

permissionAvars :: (AssertionLenses a) => Getter a [VariableID]
permissionAvars = filterAvars (== Just VTPermission)
valueAvars :: (AssertionLenses a) => Getter a [VariableID]
valueAvars = filterAvars treatAsValueJ --(\x -> (x == Just VTValue) || isNothing x)

-- |Check a first-order value formula (generating the appropriate logging events)
valueCheck :: (MonadIO m, MonadReader r m, Provers r, StringVariable v, MonadLogger m) =>
        FOF ValueAtomic v -> m (Maybe Bool)
valueCheck f = do
                let sf = varToString <$> f
                logEvent $ ProverInvocation ValueProverType (show sf)
                p <- ask
                r <- liftIO $ valueProver p sf
                logEvent $ ProverResult r
                return r

-- |Check a first-order permissions formula (generating the appropriate logging events)
permissionCheck :: (MonadIO m, MonadReader r m, Provers r, StringVariable v, MonadLogger m) =>
        FOF PermissionAtomic v -> m (Maybe Bool)
permissionCheck f = do
                let sf = varToString <$> f
                logEvent $ ProverInvocation PermissionProverType (show sf)
                p <- ask
                r <- liftIO $ permissionsProver p sf
                logEvent $ ProverResult r
                return r


-- |Check that the assertions follow from the assumptions.
checkAssertions :: (MonadIO m, MonadState s m, AssertionLenses s,
        MonadLogger m, MonadReader p m, Provers p) => m Bool
checkAssertions = do
        -- printAssertions
        bdgs <- use bindings
        asms <- use assumptions
        asts <- use assertions
        -- Check the permission assertions
        let lpermissionAssumptions = permissionConditions bdgs asms
        let permissionAssertions = permissionConditions bdgs asts
        pevs <- use permissionEvars
        pavs <- use permissionAvars
        let passt = foldr FOFExists (foldr FOFAnd FOFTrue permissionAssertions) pevs
        rp <- permissionCheck $ assumptionContext pavs lpermissionAssumptions passt
        if rp /= Just True then
                return False
            else do
                -- Check the value assertions
                let lvalueAssumptions = valueConditions bdgs asms
                let valueAssertions = valueConditions bdgs asts
                vevs <- use valueEvars
                vavs <- use valueAvars
                let vasst = foldr FOFExists (foldr FOFAnd FOFTrue valueAssertions) vevs
                rv <- valueCheck $ assumptionContext vavs lvalueAssumptions vasst
                return (rv == Just True)

justCheck :: (MonadIO m, MonadPlus m, MonadState s m, AssertionLenses s,
        MonadReader p m, MonadLogger m, Provers p) => m ()
-- ^Check that the assertions follow from the assumptions.
-- If not, fail this path
justCheck = do
        res <- checkAssertions
        unless res mzero

hypothetical :: ProverM s r m => (forall m'. (ProverM s r m') => m' a) -> m a
hypothetical mn = do
        st0 <- get
        ans <- mn
        put st0
        return ans
