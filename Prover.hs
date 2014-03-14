{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Prover where

import Prelude hiding (sequence,foldl,foldr,mapM_,mapM,elem,notElem)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.State hiding (mapM_,mapM)
import Control.Monad.Trans.Maybe
import PermissionsInterface
import Permissions
import Data.Maybe
import Data.Foldable
import Data.Traversable
import Data.Typeable
import Control.Monad hiding (mapM_,mapM)
import ProverDatatypes
import ValueProver
import qualified TypingContext as TC
import FirstOrder
import Exceptions
import Control.Lens
import Data.Functor.Identity



-- Variable identifiers
-- Strings should be alpha-numeric
data VariableID = VIDNamed String               -- To represent user-named vars
                | VIDInternal String            -- To represent internally generated vars
                | VIDExistential String         -- To represent assertion vars
                deriving (Eq,Ord,Typeable)

instance Show VariableID where
        show (VIDNamed s) = s
        show (VIDInternal s) = "__" ++ s
        show (VIDExistential s) = "_e" ++ s

vidToString :: VariableID -> String
-- Generates a String from a VariableID
-- Unlike show, this should be injective, and is used to communicate variables to provers
vidToString (VIDNamed n) = "n_" ++ n
vidToString (VIDInternal n) = "i_" ++ n
vidToString (VIDExistential n) = "e_" ++ n


-- Refreshable instance allows us to generate a 'fresh' version of a variable
instance Refreshable VariableID where
        freshen (VIDNamed s) = [VIDNamed s' | s' <- freshen s]
        freshen (VIDInternal s) = [VIDInternal s' | s' <- freshen s]
        freshen (VIDExistential s) = [VIDExistential s' | s' <- freshen s]


-- Conditions are the basic assertions and assumptions that are handled by the provers
data Condition v = PermissionCondition (FOF PermissionAtomic v)
                | ValueCondition (FOF ValueAtomic v)
                | EqualityCondition v v
                deriving (Eq, Ord)


-- The ConditionProp class allows us to convert other types to Conditions
class ConditionProp c where
        toCondition :: c v -> Condition v
        negativeCondition :: c v -> Condition v

-- First-order permission formulae are instances of ConditionProp
instance ConditionProp (FOF PermissionAtomic) where
        toCondition = PermissionCondition
        negativeCondition = PermissionCondition . FOFNot

-- First-order value formulae are instances of ConditionProp
instance ConditionProp (FOF ValueAtomic) where
        toCondition = ValueCondition
        negativeCondition = ValueCondition . FOFNot

{-- This would probably be a bad idea
instance (ConditionProp (FOF a)) => ConditionProp a where        
        toCondition = toCondition . FOFAtom
        negativeCondition = negativeCondition . FOFAtom
--}

-- Atomic permission assertions are instances of ConditionProp
instance ConditionProp PermissionAtomic where
        toCondition = toCondition . FOFAtom
        negativeCondition = negativeCondition . FOFAtom

-- Atomic value assertions are instances of ConditionProp
instance ConditionProp ValueAtomic where
        toCondition = toCondition . FOFAtom
        negativeCondition = negativeCondition . FOFAtom

-- Generalised expressions, which can refer to permissions or to values
data Expr v = PermissionExpr (PermissionExpression v)
        | ValueExpr (ValueExpression v)
        | VariableExpr v
        deriving (Eq, Ord, Functor, Foldable)

instance Show v => Show (Expr v) where
        show (PermissionExpr pe) = show pe
        show (ValueExpr ve) = show ve
        show (VariableExpr v) = show v


-- Generate an equality condition for two expressions
-- An error occurs if the expressions are clearly incomparable (Permission-Variable comparison)
exprEquality :: Expr v -> Expr v -> Condition v
exprEquality (PermissionExpr pe1) (PermissionExpr pe2) = PermissionCondition $ FOFAtom $ PAEq pe1 pe2
exprEquality (PermissionExpr pe1) (VariableExpr v2) = PermissionCondition $ FOFAtom $ PAEq pe1 (return v2)
exprEquality (ValueExpr ve1) (ValueExpr ve2) = ValueCondition $ FOFAtom $ VAEq ve1 ve2
exprEquality (ValueExpr ve1) (VariableExpr v2) = ValueCondition $ FOFAtom $ VAEq ve1 (return v2)
exprEquality (VariableExpr v1) (PermissionExpr pe2) = PermissionCondition $ FOFAtom $ PAEq (return v1) pe2
exprEquality (VariableExpr v1) (ValueExpr ve2) = ValueCondition $ FOFAtom $ VAEq (return v1) ve2
exprEquality (VariableExpr v1) (VariableExpr v2) = EqualityCondition v1 v2
exprEquality _ _ = error "Equality declared between incomparable expressions."

toValueExpr :: Show v => Expr v -> ValueExpression v
toValueExpr (ValueExpr e) = e
toValueExpr (VariableExpr v) = var v
toValueExpr e = error $ "The expression '" ++ show e ++ "' cannot be coerced to a value expression."

-- We can substitute Exprs for variables in PermissionExpressions
instance ExpressionSub PermissionExpression Expr where
        exprSub s (PEVar v) = case s v of
                        (PermissionExpr pe) -> pe
                        (VariableExpr ve) -> return ve
                        _ -> error "A permission variable was substituted by an expression that is not a permission expression."
        exprSub s (PESum x y) = PESum (exprSub s x) (exprSub s y)
        exprSub s (PECompl e) = PECompl (exprSub s e)
        exprSub _ PEFull = PEFull
        exprSub _ PEZero = PEZero

-- We can substitute Exprs for variables in ValueExpressions
instance ExpressionSub ValueExpression Expr where
        exprSub s (VEVar v) = case s v of
                        (ValueExpr ve) -> ve
                        (VariableExpr ve) -> return ve
                        _ -> error "A value variable was substituted by an expression that is not a value expression."
        exprSub s (VEConst k) = VEConst k
        exprSub s (VEPlus e1 e2) = VEPlus (exprSub s e1) (exprSub s e2)
        exprSub s (VEMinus e1 e2) = VEMinus (exprSub s e1) (exprSub s e2)
        exprSub s (VETimes e1 e2) = VETimes (exprSub s e1) (exprSub s e2)

instance Expression Expr where
        var = VariableExpr

-- Note, I'm slightly concerned that this might not satisfy
-- all the monad laws in some undefined cases.
instance Monad Expr where
        return = VariableExpr
        (PermissionExpr pe) >>= s = PermissionExpr $ exprSub s pe
        (ValueExpr ve) >>= s = ValueExpr $ exprSub s ve
        (VariableExpr v) >>= s = s v

instance FreeVariables Expr where
        foldrFree f x e = foldr f x e

class ProverExpression c where
        toExpr :: c v -> Expr v

instance ProverExpression PermissionExpression where
        toExpr = PermissionExpr

instance ProverExpression ValueExpression where
        toExpr = ValueExpr

instance ProverExpression Identity where
        toExpr = VariableExpr . runIdentity

integerExpr = ValueExpr . VEConst

instance FreeVariables Condition where
        foldrFree f x (PermissionCondition fof) = foldrFree f x fof
        foldrFree f x (ValueCondition fof) = foldrFree f x fof
        foldrFree f x (EqualityCondition a b) = foldr f x [a,b]
        

instance Show v => Show (Condition v) where
        show (PermissionCondition pa) = show pa
        show (ValueCondition va) = show va
        show (EqualityCondition v1 v2) = show v1 ++ " = " ++ show v2

instance ExpressionCASub Condition Expr where
        exprCASub s (PermissionCondition pc) = PermissionCondition $ exprCASub s pc
        exprCASub s (ValueCondition vc) = ValueCondition $ exprCASub s vc
        exprCASub s (EqualityCondition v1 v2) = exprEquality (s v1) (s v2)



type BindingContext = TC.TContext VariableID VariableType

{- TODO: tag assumptions with a 'corollary' flag to indicate
 - if it is a consequence of other assumptions.  Some types
 - of prover may work better without corollaries.  For instance,
 - the internal permissions prover will most likely waste time
 - with corollaries.
 -}

data Assumptions = Assumptions {
        _bindings :: BindingContext,
        _assumptions :: [Condition VariableID]
        }
makeLenses ''Assumptions

instance Show Assumptions where
        show ass = foldl (++) "" $ map (('\n':) . show) $ ass ^. assumptions

emptyAssumptions :: Assumptions
emptyAssumptions = Assumptions TC.empty []

type ProverT = StateT Assumptions
-- Invariant: All variables occuring free in assumptions MUST be bound in bindings

runProverT :: (Monad m) => ProverT m a -> m a
-- run a ProverT from emptyAssumptions
runProverT p = evalStateT p emptyAssumptions

-- Can I be bothered to use this monad?
-- type Proving m = ReaderT Provers (ProverT m)

doBindVarsAs :: (Monad m, Foldable f) => Simple Lens a BindingContext -> f VariableID -> VariableType -> StateT a m ()
doBindVarsAs l s vt = do
                        b0 <- use l
                        bs <- runEMT $ TC.bindAll s vt b0 `catch` (\(e :: TypeUnificationException VariableID VariableType) -> error (show e))
                        l .= bs

bindVarsAs :: (Monad m, Foldable f) => f VariableID -> VariableType -> ProverT m ()
bindVarsAs = doBindVarsAs bindings

doUnifyEqVars :: (Monad m) => Simple Lens a BindingContext -> VariableID -> VariableID -> StateT a m ()
doUnifyEqVars l v1 v2 = do
                        b0 <- use l
                        bs <- runEMT $ TC.unify v1 v2 b0 `catch` (\(e :: TypeUnificationException VariableID VariableType) -> error (show e))
                        l .= bs


unifyEqVars :: (Monad m) => VariableID -> VariableID -> ProverT m ()
unifyEqVars = doUnifyEqVars bindings
declareVars :: (Monad m, Foldable f) => f VariableID -> ProverT m ()
declareVars s = bindings %= TC.declareAll s


checkExpressionAtType :: Monad m => Expr VariableID -> VariableType -> ProverT m ()
-- Check that the expression is of the appropriate type,
-- binding the variables to be sure they are not inconsistently used
-- First two cases are straightforward
checkExpressionAtType (PermissionExpr c) VTValue = error $ "A value expression was expected, but '" ++ show c ++ "' is a permission expression."
checkExpressionAtType (ValueExpr c) VTPermission = error $ "A permission expression was expected, but '" ++ show c ++ "' is a value expression."
checkExpressionAtType e VTValue = bindVarsAs (freeVariables e) VTValue
checkExpressionAtType e VTPermission = bindVarsAs (freeVariables e) VTPermission

isBound :: (Monad m) => VariableID -> ProverT m Bool
-- Determine if the given variable is bound.
isBound v = do
                b <- use bindings
                return $ TC.lookup v b /= TC.NotBound


-- Only use internally
addAssumption :: (Monad m) => Condition VariableID -> ProverT m ()
addAssumption c = assumptions %= (c :)

assume :: Monad m => Condition VariableID -> ProverT m ()
-- Add a condition to the list of assumptions, binding its
-- variables at the appropriate type.  This can raise an
-- error if a variable is not used with a consistent type.
assume c@(PermissionCondition pass) = do
                        bindVarsAs (freeVariables c) VTPermission
                        addAssumption c
assume c@(ValueCondition cass) = do
                        bindVarsAs (freeVariables c) VTValue
                        addAssumption c
assume c@(EqualityCondition v1 v2) = do
                        unifyEqVars v1 v2
                        addAssumption c

assumeTrue :: (ConditionProp c, Monad m) => c VariableID -> ProverT m ()
assumeTrue = assume . toCondition

assumeFalse :: (ConditionProp c, Monad m) => c VariableID -> ProverT m ()
assumeFalse = assume . negativeCondition


permissionConditions :: (Ord v) => TC.TContext v VariableType -> [Condition v] -> [FOF PermissionAtomic v]
permissionConditions tc [] = []
permissionConditions tc (PermissionCondition pa : xs) = pa : permissionConditions tc xs
permissionConditions tc (EqualityCondition v1 v2 : xs) = if TC.lookup v1 tc == TC.JustType VTPermission then (FOFAtom $ PAEq (PEVar v1) (PEVar v2)) : permissionConditions tc xs else permissionConditions tc xs
permissionConditions tc (_ : xs) = permissionConditions tc xs


-- WARNING: don't use these in a CheckT context!
-- The types in the Assumptions may be outdated by those in the Assertions
permissionAssumptions :: Assumptions -> [FOF PermissionAtomic VariableID]
-- Extract the assumptions pertaining to permissions
permissionAssumptions ass = permissionConditions (ass ^. bindings) (ass ^. assumptions)

permissionVariables :: Assumptions -> [VariableID]
-- Return a list of the permission variables
permissionVariables = Map.keys . Map.filter (== Just VTPermission) . TC.toMap . _bindings

valueConditions :: (Ord v) => TC.TContext v VariableType -> [Condition v] -> [FOF ValueAtomic v]
valueConditions tc [] = []
valueConditions tc (EqualityCondition v1 v2 : xs) =
                if let t = TC.lookup v1 tc in t == TC.JustType VTValue || t == TC.Undetermined then
                        (FOFAtom $ VAEq (var v1) (var v2)) : valueConditions tc xs
                else
                        valueConditions tc xs
valueConditions tc (ValueCondition cass : xs) = cass : valueConditions tc xs
valueConditions tc (_ : xs) = valueConditions tc xs

valueAssumptions :: Assumptions -> [FOF ValueAtomic VariableID]
-- Extract the assumptions pertaining to values (integers)
-- Equality assumptions where the variable type is indeterminate are treated as value assumptions
valueAssumptions ass = valueConditions (ass ^. bindings) (ass ^. assumptions)

valueVariables :: Assumptions -> [VariableID]
-- Return a list of value variables; variables with no other type are treated as value variables
valueVariables = Map.keys . Map.filter (\x -> (x == Just VTValue) || (x == Nothing)) . TC.toMap . _bindings

checkConsistency :: (Functor a, Foldable a) => (FOF a String -> IO (Maybe Bool)) -> [VariableID] -> [FOF a VariableID] -> IO (Maybe Bool)
-- Given a first-order prover, check whether a list of assertions (with free variables from a given list) is consistent.
-- Consistent if the formula ¬(E) x1, ..., xn . P1 /\ ... /\ Pm /\ True is invalid. 
checkConsistency p vars asss = do
                        rp <- p $ FOFNot $ fmap vidToString $ foldr FOFExists (foldr FOFAnd FOFTrue asss) vars
                        return $ fmap not rp

isConsistent :: (MonadIO m) => Provers -> ProverT m (Maybe Bool)
-- Check whether the current set of assumptions is consistent
-- (i.e. False does not follow)
isConsistent ps = get >>= ic
        where
                ic ass = liftIO $ do
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
-- Wrap universal quantifiers and assumptions around an assertion
assumptionContext vids asms ast = foldr FOFForAll (foldr FOFImpl ast asms) vids


{--
 - So I was thinking of effectively binding existential variables
 - to values and doing substitutions with these.  This may have
 - the benefit of reducing the number of variables that are introduced.
 - However it would probably be better to implement solver simplifiers
 - that eliminate extraneous variables.  (Something to do later, when
 - performance goes to hell.)
 - Instead, you'll just have to introduce existential variables and
 - make assertions about them being equal to things.
 --}

data Assertions = Assertions {
        -- Context that binds both assumption and assertion variables to their types
        _variableTypes :: BindingContext,
        -- The initial assumptions
        _initialAssumptions :: Assumptions,
        -- List of assertions
        _assertions :: [Condition VariableID]
        }
makeLenses ''Assertions

instance Show Assertions where
        show asts = "Assumptions: !["
                ++ show (TC.intersection (asts ^. variableTypes) (asts ^. initialAssumptions ^. bindings))
                ++ "] "
                ++ show (asts ^. initialAssumptions ^. assumptions)
                ++ "\nAssertions: ?["
                ++ show (TC.difference (asts ^. variableTypes) (asts ^. initialAssumptions ^. bindings))
                ++ "] "
                ++ show (asts ^. assertions)

emptyAssertions :: Assumptions -> Assertions
emptyAssertions asmts = Assertions (asmts ^. bindings) asmts []

type CheckerT = StateT Assertions
{--
showCheckerT :: Monad m => CheckerT m String
showCheckerT = do
                asts <- get
                return $ "Assumptions: !" ++ show ( Map.intersection (TC.toMap $ asts ^. variableTypes) (TC.toMap $ asts ^. initialAssumptions ^. bindings) ) ++ " " ++ show (asts ^. initialAssumptions ^. assumptions) ++ "\nAssertions: ?" ++ show ( Map.intersection (TC.toMap $ asts ^. variableTypes) (TC.toMap $ asts ^. initialAssumptions ^. bindings) ) ++ " " ++ show (asts ^. assertions)
--}

printCheckerT :: (MonadIO m, Monad m) => CheckerT m ()
printCheckerT = get >>= liftIO . print

bindAtExprType :: VariableID -> Expr VariableID -> TC.TContext VariableID VariableType -> TC.TContext VariableID VariableType
bindAtExprType v (PermissionExpr _) c = runEM $ TC.bind v VTPermission c `catch` (\(e :: TypeUnificationException VariableID VariableType) -> error (show e))
bindAtExprType v (ValueExpr _) c = runEM $ TC.bind v VTValue c `catch` (\(e :: TypeUnificationException VariableID VariableType) -> error (show e))
bindAtExprType v (VariableExpr v') c = runEM $ TC.unify v v' c `catch` (\(e :: TypeUnificationException VariableID VariableType) -> error (show e))

newEvar :: Monad m => String -> CheckerT m VariableID
-- Generate a new assertion variable with a name like the one given
-- WARNING: No other mechanism should generate VIDExistential variables.
newEvar vname = do
                vt <- use variableTypes
                let evin = TC.firstFresh [ VIDExistential $ vname ++ suffix | suffix <- "" : map show [0..] ] vt
                variableTypes %= TC.declare evin
                return evin

bindVarsAsCk :: (Monad m, Foldable f) => f VariableID -> VariableType -> CheckerT m ()
bindVarsAsCk = doBindVarsAs variableTypes

unifyEqVarsCk :: (Monad m) => VariableID -> VariableID -> CheckerT m ()
unifyEqVarsCk = doUnifyEqVars variableTypes

assert :: Monad m => Condition VariableID -> CheckerT m ()
-- Assert that a given condition holds
-- We assume that all of the variables are already bound correctly
assert c@(PermissionCondition _) = do
                        bindVarsAsCk (freeVariables c) VTPermission
                        assertions %= (c :)
assert c@(ValueCondition _) = do
                        bindVarsAsCk (freeVariables c) VTValue
                        assertions %= (c :)
assert c@(EqualityCondition v1 v2) = do
                        unifyEqVarsCk v1 v2
                        assertions %= (c :)

assertEqual :: (ProverExpression e, Monad m) => e VariableID -> e VariableID -> CheckerT m ()
assertEqual e1 e2 = assert $ exprEquality (toExpr e1) (toExpr e2)



assertTrue :: (ConditionProp c, Monad m) => c VariableID -> CheckerT m ()
assertTrue = assert . toCondition

assertFalse :: (ConditionProp c, Monad m) => c VariableID -> CheckerT m ()
assertFalse = assert . negativeCondition


makeEquality :: v -> Expr v -> Condition v
-- Given a variable and an expression, generate a condition that
-- equates the variable with the expression
makeEquality v (PermissionExpr pe) = PermissionCondition $ FOFAtom $ PAEq (var v) pe
makeEquality v (ValueExpr ve) = ValueCondition $ FOFAtom $ VAEq (var v) ve
makeEquality v (VariableExpr ve) = EqualityCondition v ve

{--
bindEvar :: Monad m => VariableID -> Expr VariableID -> CheckerT m ()
-- Binds an evar to an expression (in existing variables).
-- If there already is a binding, this generates a condition
-- that the bound expressions be equal.
-- The variable MUST have been generated by newEvar
-- WARNING: this may be risky with side-effecting expressions (namely permission composition)
bindEvar ev expr = do
                variableTypes %= bindAtExprType ev expr
                curbinding <- use evExprs
                if ev `Map.member` curbinding then
                                assert $ makeEquality ev expr
                        else
                                evExprs %= Map.insert ev expr

type EvarSubstitution = VariableID -> Expr VariableID

assertionsSubstitution :: Assertions -> EvarSubstitution
assertionsSubstitution assts v = Map.findWithDefault (return v) v (assts ^. evExprs)
--}

filterEvars :: (Maybe VariableType -> Bool) -> Assertions -> [VariableID]
filterEvars f asts = let asms = asts ^. initialAssumptions in
        Map.keys $ Map.filter f $ TC.toMap $ TC.difference (asts ^. variableTypes) (asms ^. bindings)

permissionEvars = filterEvars (== Just VTPermission)
valueEvars = filterEvars (\x -> (x == Just VTValue) || (x == Nothing))

filterAvars :: (Maybe VariableType -> Bool) -> Assertions -> [VariableID]
filterAvars f asts = let asms = asts ^. initialAssumptions in
        Map.keys $ Map.filter f $ Map.intersection (TC.toMap $ asts ^. variableTypes) (TC.toMap $ asms ^. bindings)

permissionAvars = filterAvars (== Just VTPermission)
valueAvars = filterAvars (\x -> (x == Just VTValue) || (x == Nothing))

justCheck :: (MonadIO m, MonadPlus m) => Provers -> CheckerT m ()
-- Check that the assertions follow from the assumptions
-- If not, fail this path
justCheck ps = do
        printCheckerT
        assts <- get
        -- Check the permission assertions
        let lpermissionAssumptions = permissionConditions (assts ^. variableTypes) (assts ^. initialAssumptions ^. assumptions)
        let permissionAssertions = permissionConditions (assts ^. variableTypes) (assts ^. assertions)
        let passt = foldr FOFExists (foldr FOFAnd FOFTrue permissionAssertions) (permissionEvars assts)
        liftIO $ print $ fmap vidToString $ assumptionContext (permissionAvars assts) lpermissionAssumptions passt
        rp <- liftIO $ permissionsProver ps $ fmap vidToString $ assumptionContext (permissionAvars assts) lpermissionAssumptions passt
        if rp /= Just True then
                mzero
        else do
                -- Check the value assertions
                let lvalueAssumptions = valueConditions (assts ^. variableTypes) (assts ^. initialAssumptions ^. assumptions)
                let valueAssertions = valueConditions (assts ^. variableTypes) (assts ^. assertions)
                let vasst = foldr FOFExists (foldr FOFAnd FOFTrue valueAssertions) (valueEvars assts)
                rv <- liftIO $ valueProver ps $ fmap vidToString $ assumptionContext (valueAvars assts) lvalueAssumptions vasst
                liftIO $ print $ fmap vidToString $ assumptionContext (valueAvars assts) lvalueAssumptions vasst
                liftIO $ print rv
                if rv /= Just True then mzero else return ()

admitChecks :: (Monad m) => CheckerT m a -> ProverT m a
-- Admit the assumptions as assertions
admitChecks c = do
                        ams <- get
                        (r, assts) <- lift $ runStateT c (emptyAssertions ams)
                        bindings .= assts ^. variableTypes
                        assumptions %= (assts ^. assertions ++)
                        return r

check :: (MonadIO m, MonadPlus m) => CheckerT m a -> Provers -> ProverT m a
-- Check that the assertions follow from the assumptions
-- If so, admit them as assumptions, returning the substitution of evars
-- If not, fail this path
check c ps = admitChecks $ do
                        r <- c
                        justCheck ps
                        return r

-- Instantiator should be used for introducing existential variables
-- for use in the symbolic execution of a specification.

newtype Instantiator m a = Instantiator {
                runInstantiator :: StateT (Map.Map String VariableID) (CheckerT m) a
        } deriving (Monad, MonadIO, Functor, MonadFix, MonadPlus)

instantiate :: (Monad m, Traversable f) => f String -> Instantiator m (f VariableID)
-- Generate fresh existential variables for each name
instantiate = mapM $ \s -> Instantiator $ do
                v <- liftM (Map.lookup s) get
                case v of
                        Nothing -> do
                                vv <- lift $ newEvar s
                                modify (Map.insert s vv)
                                return vv
                        (Just vv) -> return vv

doInstantiation :: (Monad m) => Instantiator m a -> CheckerT m a
doInstantiation i = evalStateT (runInstantiator i) Map.empty

doDeclareNames :: (Monad m, Traversable f) => Simple Lens a BindingContext -> f String -> StateT a m (f VariableID)
doDeclareNames l = mapM $ \s -> do
                let v = VIDNamed s
                l %= TC.declare v
                return v


declareAssertionNames :: (Monad m, Traversable f) => f String -> CheckerT m (f VariableID)
declareAssertionNames = doDeclareNames variableTypes

declareAssumptionNames :: (Monad m, Traversable f) => f String -> ProverT m (f VariableID)
declareAssumptionNames = doDeclareNames bindings

