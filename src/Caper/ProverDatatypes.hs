
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Caper.ProverDatatypes (
        module Caper.FreeVariables,
        module Caper.ProverDatatypes) where
import Prelude hiding (sequence,foldl,foldr,elem,mapM_,mapM,notElem)
-- -- import Control.Applicative
import Control.Monad.State hiding (mapM_,mapM)
import Control.Arrow
import Data.Foldable
-- -- import Data.Traversable
import Data.Typeable
import Data.Either
import Data.Functor.Identity
import qualified Data.Map as Map
import qualified Data.Set as Set

import Caper.FreeVariables

{-# ANN module "HLint: ignore Eta reduce" #-}

class Refreshable v where
        freshen :: v -> [v]

nearFreshen :: Refreshable v => v -> [v]
nearFreshen = ap (:) freshen

freshWRT :: (Refreshable v, Eq v, Foldable t) => v -> t v -> v
freshWRT v e = head [vv | vv <- v : freshen v, vv `notElem` e]

freshWRTFree :: (Refreshable v, Ord v, FreeVariables s v) => v -> s -> v
freshWRTFree v e = freshWRT v (freeVariables e)

instance Refreshable String where
        freshen s = [ s ++ show x | x <- [0 :: Int ..] ]

instance Refreshable v => Refreshable (Either v v) where
        freshen (Left vr) = map Left (freshen vr)
        freshen (Right vr) = map Right (freshen vr)

freshSub :: (Refreshable v, Eq v, Ord v, Foldable f, Foldable g) => f v -> g v -> v -> v
-- ^Given a collection of variables to refresh, and a collection that they
-- should be fresh with respect to, produces a function that substitutes
-- the old variables for the fresh ones (leaving others alone).  This
-- substitution should only really be applied to variables in the second collection.
freshSub rvs wrtvs = \v -> Map.findWithDefault v v (foldl frshmp Map.empty rvs)
        where
                frshmp mp v = if Map.member v mp then mp else
                                Map.insert v (head [vs | vs <- freshen v, vs `notElem` wrtvs]) mp

data Literal a v = LPos (a v) | LNeg (a v) deriving (Functor, Foldable, Traversable, Eq, Ord)

instance Show (a v) => Show (Literal a v) where
        show (LPos x) = show x
        show (LNeg x) = "\xAC " ++ show x

instance FreeVariables (a v) v => FreeVariables (Literal a v) v where
    foldrFree f x (LPos e) = foldrFree f x e
    foldrFree f x (LNeg e) = foldrFree f x e

data PermissionExpression v = PEFull
                        | PEZero
                        | PEVar v
                        | PESum (PermissionExpression v) (PermissionExpression v)
                        | PECompl (PermissionExpression v)
                        deriving (Eq,Ord,Functor,Foldable,Traversable,Show)
{-
instance Show v => Show (PermissionExpression v) where
        show PEFull = "1"
        show PEZero = "0"
        show (PESum e1 e2) = "(" ++ show e1 ++ " + " ++ show e2 ++ ")"
        show (PECompl e) = "(1 - " ++ show e ++ ")"
        show (PEVar v) = show v
-}

instance Monad PermissionExpression where
        return = PEVar
        (PEVar v) >>= b = b v
        PESum x y >>= b = PESum (x >>= b) (y >>= b)
        PECompl e >>= b = PECompl (e >>= b)
        PEFull >>= _ = PEFull
        PEZero >>= _ = PEZero

instance Applicative PermissionExpression where
        pure = return
        (<*>) = ap

-- Note: could probably get rid of Expression and use Monad instead: return takes place of var
class Expression e where
        var :: v -> e v

instance Expression PermissionExpression where
        var = PEVar

data PermissionAtomic v =
                 PAEq (PermissionExpression v) (PermissionExpression v)
                | PADis (PermissionExpression v) (PermissionExpression v)
                | PALte (PermissionExpression v) (PermissionExpression v)
                deriving (Functor, Foldable, Traversable, Eq, Ord, Show)

class ExpressionSub c e where
        exprSub :: (v -> e w) -> c v -> c w

instance Monad m => ExpressionSub m m where
        exprSub a b = b >>= a

instance ExpressionSub PermissionExpression e => ExpressionSub PermissionAtomic e where
        exprSub s (PAEq x y) = PAEq (exprSub s x) (exprSub s y)
        exprSub s (PADis x y) = PADis (exprSub s x) (exprSub s y)
        exprSub s (PALte x y) = PALte (exprSub s x) (exprSub s y)

{-
instance Show v => Show (PermissionAtomic v) where
        show (PAEq v1 v2) = show v1 ++ " =p= " ++ show v2
        show (PADis v1 v2) = show v1 ++ " # " ++ show v2
-}

type PermissionLiteral = Literal PermissionAtomic

instance (ExpressionSub a e) => ExpressionSub (Literal a) e where
        exprSub s (LPos a) = LPos (exprSub s a)
        exprSub s (LNeg a) = LNeg (exprSub s a)


data ValueExpression v =
          VEConst Integer
        | VEVar v
        | VEPlus (ValueExpression v) (ValueExpression v)
        | VEMinus (ValueExpression v) (ValueExpression v)
        | VETimes (ValueExpression v) (ValueExpression v)
        deriving (Eq,Ord,Functor,Foldable,Traversable)

instance Expression ValueExpression where
        var = VEVar

instance Monad ValueExpression where
        return = VEVar
        (VEConst c) >>= _ = VEConst c
        (VEVar v) >>= b = b v
        VEPlus e1 e2 >>= b = VEPlus (e1 >>= b) (e2 >>= b)
        VEMinus e1 e2 >>= b = VEMinus (e1 >>= b) (e2 >>= b)
        VETimes e1 e2 >>= b = VETimes (e1 >>= b) (e2 >>= b)

instance Applicative ValueExpression where
        pure = return
        (<*>) = ap

instance Show a => Show (ValueExpression a) where
        show (VEConst n) = show n
        show (VEVar v) = show v
        show (VEPlus e1 e2) = "(" ++ show e1 ++ " + " ++ show e2 ++  ")"
        show (VEMinus (VEConst 0) e2) = "(-" ++ show e2 ++ ")"
        show (VEMinus e1 e2) = "(" ++ show e1 ++ " - " ++ show e2 ++  ")"
        show (VETimes e1 e2) = "(" ++ show e1 ++ " * " ++ show e2 ++  ")"

data ValueAtomic v =
          VAEq (ValueExpression v) (ValueExpression v)
        | VALt (ValueExpression v) (ValueExpression v)
        deriving (Eq,Ord,Functor,Foldable,Traversable)

instance ExpressionSub ValueExpression e => ExpressionSub ValueAtomic e where
        exprSub s (VAEq v1 v2) = VAEq (exprSub s v1) (exprSub s v2)
        exprSub s (VALt v1 v2) = VALt (exprSub s v1) (exprSub s v2)


instance Show a => Show (ValueAtomic a) where
        show (VAEq e1 e2) = show e1 ++ " = " ++ show e2
        show (VALt e1 e2) = show e1 ++ " < " ++ show e2

class ValueExpressionCastable t v where
        toValueExpr :: t v -> ValueExpression v

instance ValueExpressionCastable ValueExpression v where
        toValueExpr = id


($+$) :: (ValueExpressionCastable a v, ValueExpressionCastable b v) => a v -> b v -> ValueExpression v
($+$) x y = toValueExpr x `VEPlus` toValueExpr y
($-$) :: (ValueExpressionCastable a v, ValueExpressionCastable b v) => a v -> b v -> ValueExpression v
($-$) x y = toValueExpr x `VEMinus` toValueExpr y
($*$) :: (ValueExpressionCastable a v, ValueExpressionCastable b v) => a v -> b v -> ValueExpression v
($*$) x y = toValueExpr x `VETimes` toValueExpr y

infixl 6 $+$, $-$
infixl 6 $*$

{-
instance Num (ValueExpression v) where
        (+) = VEPlus
        (-) = VEMinus
        (*) = VETimes
        fromInteger = VEConst
-}

class StringVariable v where
        -- |Convert a variable to a string, for passing to a prover
        -- Each variable should have a unique string representation:
        -- if two variables have the same representation, they are
        -- considered to be the same variable.
        -- Care should be taken to ensure that variables conform to
        -- syntax restrictions: [a-zA-Z0-9_]* 
        varToString :: v -> String
        -- |Convert a string to a variable.  As a precondition, the
        -- string should conform to the syntax restriction: [a-zA-Z0-9_]*
        -- Note that in general converting to and from a string will not
        -- give an identity operation (and vice-versa).
        varFromString :: String -> v

data VariableType = VTPermission | VTValue | VTRegionID
        deriving (Eq, Ord, Typeable)

instance Show VariableType where
        show VTPermission = "permission"
        show VTValue = "value"
        show VTRegionID = "region identifier"


type PermissionsProver = FOF PermissionAtomic String -> IO (Maybe Bool)
data ValueProver =
        VPBasic (FOF ValueAtomic String -> IO (Maybe Bool))
        | VPEnhanced (FOF ValueAtomic String -> IO (Maybe Bool)) ([FOF ValueAtomic VariableID] -> FOF ValueAtomic VariableID -> IO (Maybe Bool))

class Provers a where
        permissionsProver :: a -> PermissionsProver
        valueProver :: a -> ValueProver

data ProverRecord = Provers {
                _permissionsProver :: PermissionsProver,
                _valueProver :: ValueProver,
                _permissionsInfo :: IO String,
                _valueInfo :: IO String
                }

instance Provers ProverRecord where
        permissionsProver = _permissionsProver
        valueProver = _valueProver



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

instance StringVariable VariableID where
        -- Generates a String from a VariableID
        -- Unlike show, this should be injective, and is used to communicate variables to provers
        varToString (VIDNamed n) = "n_" ++ n
        varToString (VIDInternal n) = "i_" ++ n
        varToString (VIDExistential n) = "e_" ++ n
        varFromString n = VIDInternal n


-- Refreshable instance allows us to generate a 'fresh' version of a variable
instance Refreshable VariableID where
        freshen (VIDNamed s) = [VIDNamed s' | s' <- freshen s]
        freshen (VIDInternal s) = [VIDInternal s' | s' <- freshen s]
        freshen (VIDExistential s) = [VIDExistential s' | s' <- freshen s]




data FOF a v =
          FOFForAll v (FOF a v)
        | FOFExists v (FOF a v)
        | FOFAtom (a v)
        | FOFAnd (FOF a v) (FOF a v)
        | FOFOr (FOF a v) (FOF a v)
        | FOFImpl (FOF a v) (FOF a v)
        | FOFNot (FOF a v)
        | FOFFalse
        | FOFTrue
        deriving (Eq, Ord, Functor, Foldable, Traversable)
        
instance (Show (a v), Show v) => Show (FOF a v) where
        show FOFFalse = "_|_"
        show FOFTrue = "T"
        show (FOFAtom a) = show a
        show (FOFNot f) = "\xAC " ++ show f
        show (FOFAnd f1 f2) = "(" ++ show f1 ++ " /\\ " ++ show f2 ++ ")"
        show (FOFOr f1 f2) = "(" ++ show f1 ++ " \\/ " ++ show f2 ++ ")"
        show (FOFImpl f1 f2) = "(" ++ show f1 ++ " => " ++ show f2 ++ ")"
        show (FOFForAll v f1) = "![" ++ show v ++ "](" ++ show f1 ++ ")"
        show (FOFExists v f1) = "?[" ++ show v ++ "](" ++ show f1 ++ ")"

instance (Foldable a) => FreeVariables (FOF a b) b where
        foldrFree f = ff []
                where
                        ff bound x (FOFForAll v s) = ff (v : bound) x s
                        ff bound x (FOFExists v s) = ff (v : bound) x s
                        ff bound x (FOFAtom a) = foldr (ignoring bound) x a
                        ff bound x (FOFAnd f1 f2) = ff bound (ff bound x f2) f1
                        ff bound x (FOFOr f1 f2) = ff bound (ff bound x f2) f1
                        ff bound x (FOFImpl f1 f2) = ff bound (ff bound x f2) f1
                        ff bound x (FOFNot f') = ff bound x f'
                        ff _ x _ = x
                        ignoring l u v = if u `elem` l then v else f u v

literalToFOF :: Literal a v -> FOF a v
literalToFOF (LPos a) = FOFAtom a
literalToFOF (LNeg a) = FOFNot $ FOFAtom a

-- |This class provides capture-avoiding substitution
class ExpressionCASub c e where
        -- |Apply a substitution function on the free variables, renaming the bound variables to avoid capture
        exprCASub :: (Refreshable v, Ord v) => (v -> e v) -> c v -> c v
        -- |Apply a substitution function on the free variables (mapping to a new variable type), renaming the
        -- bound variables to avoid capture.
        exprCASub' :: (Refreshable w, Ord v, Ord w, StringVariable v, StringVariable w) => (v -> e w) -> c v -> c w

instance ExpressionCASub c e => ExpressionCASub (Literal c) e where
        exprCASub s (LPos c) = LPos $ exprCASub s c
        exprCASub s (LNeg c) = LNeg $ exprCASub s c
        exprCASub' s (LPos c) = LPos $ exprCASub' s c
        exprCASub' s (LNeg c) = LNeg $ exprCASub' s c

-- |Helper function for capture-avoiding substitution in 'FOF'.
-- A bound variable @v@ is mapped to @Left v@.
-- Unbound variables @w@ are substituted to @Right <$> subFun w@.
helpFOFSub :: forall a e v w. (ExpressionSub a e, Functor a, Foldable a, Functor e, Applicative e, Eq v, Eq w) =>
        (v -> e w)      -- ^Substitution
        -> (v -> Bool)  -- ^Determine if variable is bound
        -> FOF a v      -- ^Formula to substitute in
        -> FOF a (Either v w)
helpFOFSub subFun isBnd0 = helpSub isBnd0
        where
                helpSub isBnd (FOFForAll v p) = FOFForAll (Left v) (helpSub (\x -> x == v || isBnd x) p)
                helpSub isBnd (FOFExists v p) = FOFExists (Left v) (helpSub (\x -> x == v || isBnd x) p)
                helpSub isBnd (FOFAtom a) = FOFAtom (exprSub (\v -> if isBnd v then pure (Left v) else fmap Right (subFun v)) a)
                helpSub isBnd (FOFAnd p1 p2) = FOFAnd (helpSub isBnd p1) (helpSub isBnd p2)
                helpSub isBnd (FOFOr p1 p2) = FOFOr (helpSub isBnd p1) (helpSub isBnd p2)
                helpSub isBnd (FOFImpl p1 p2) = FOFImpl (helpSub isBnd p1) (helpSub isBnd p2)
                helpSub isBnd (FOFNot p) = FOFNot (helpSub isBnd p)
                helpSub _ FOFFalse = FOFFalse
                helpSub _ FOFTrue = FOFTrue


refreshLefts :: (Functor a, Foldable a, Ord v, Ord w) => (v -> [w]) -> a (Either v w) -> a w
refreshLefts frsh s = fmap sb s
        where
                (lfts, rgts) = Set.fromList *** Set.fromList $ partitionEithers $ toList s
                fStep (mp, rgs) v = let w = head [w | w <- frsh v, w `notElem` rgs] in
                                        (Map.insert v w mp, Set.insert w rgs)
                (fmp, _) = foldl fStep (Map.empty, rgts) lfts
                sb (Left v) = Map.findWithDefault (error "no substitution for variable") v fmp
                sb (Right w) = w

{-
debugSomething :: (Show (f String), Ord v, Foldable f, Functor f) => f v -> f v
debugSomething sthg = trace (show sthg') sthg
        where
                updMap (m0, n) v
                        | v `Map.member` m0 = (m0, n)
                        | otherwise         = (Map.insert v (show n) m0, n+1)
                (mp,_) = foldl updMap (Map.empty,0) sthg
                sthg' = fmap (\v -> Map.findWithDefault (error "") v mp) sthg
-}

instance (ExpressionSub a e, Functor a, Foldable a, Functor e, Monad e) => ExpressionCASub (FOF a) e where
        exprCASub s0 = refreshLefts nearFreshen . helpFOFSub s0 (const False)
        exprCASub' s0 = refreshLefts (nearFreshen . varFromString . varToString) . helpFOFSub s0 (const False)

($=$) :: (ValueExpressionCastable a v, ValueExpressionCastable b v) => a v -> b v -> FOF ValueAtomic v
($=$) x y = FOFAtom $ toValueExpr x `VAEq` toValueExpr y
($/=$) :: (ValueExpressionCastable a v, ValueExpressionCastable b v) => a v -> b v -> FOF ValueAtomic v
($/=$) x y = FOFNot $ FOFAtom $ toValueExpr x `VAEq` toValueExpr y
($<$) :: (ValueExpressionCastable a v, ValueExpressionCastable b v) => a v -> b v -> FOF ValueAtomic v
($<$) x y = FOFAtom $ toValueExpr x `VALt` toValueExpr y
($<=$) :: (ValueExpressionCastable a v, ValueExpressionCastable b v) => a v -> b v -> FOF ValueAtomic v
($<=$) x y = FOFNot $ FOFAtom $ toValueExpr y `VALt` toValueExpr x

infix 4 $=$, $/=$, $<$, $<=$

-- |'SetExpression's represent sets of values. 
data SetExpression v =
        SetBuilder v (FOF ValueAtomic v)
        | SetSingleton (ValueExpression v)
            deriving (Eq, Ord, Functor, Foldable, Traversable)

instance Show v => Show (SetExpression v) where
    show (SetBuilder v e) = "{ " ++ show v ++ " | " ++ show e ++ " }"
    show (SetSingleton e) = "{ " ++ show e ++ " }"

instance FreeVariables (SetExpression v) v where
    foldrFree f x (SetBuilder v' cond) = foldrFree (\v -> if v == v' then id else f v) x cond
    foldrFree f x (SetSingleton e) = foldr f x e

instance (ExpressionSub ValueExpression e, Functor e, Monad e) => ExpressionCASub SetExpression e where
    exprCASub s (SetBuilder v e) = refreshLefts nearFreshen $ SetBuilder (Left v) $ helpFOFSub s (==v) e
    exprCASub s (SetSingleton e) = SetSingleton $ exprSub s e
    exprCASub' s (SetBuilder v e) = refreshLefts (nearFreshen . varFromString . varToString) $
                                        SetBuilder (Left v) $ helpFOFSub s (==v) e
    exprCASub' s (SetSingleton e) = SetSingleton $ exprSub s e

-- |The empty set.
emptySet :: StringVariable v => SetExpression v
emptySet = SetBuilder (varFromString "n") FOFFalse

-- |The set of all values.
fullSet :: StringVariable v => SetExpression v
fullSet = SetBuilder (varFromString "n") FOFTrue

toSetBuilder :: (StringVariable v, Refreshable v, Eq v) => SetExpression v -> SetExpression v
toSetBuilder se = SetBuilder v c
        where
            (v, c) = case se of
                SetBuilder v0 c0 -> (v0, c0)
                SetSingleton e -> let v0 = varFromString "n" `freshWRT` e in (v0, FOFAtom $ VAEq (var v0) e)

setUnion :: (StringVariable v, Refreshable v, Ord v) => SetExpression v -> SetExpression v -> SetExpression v
setUnion a0 b0 = case (toSetBuilder a0, toSetBuilder b0) of
        ss@(SetBuilder va ca, SetBuilder vb cb) -> 
            let v = va `freshWRTFree` ss in
            SetBuilder v (FOFOr (exprCASub (\v' -> VEVar $ if v' == va then v else v') ca)
                                (exprCASub (\v' -> VEVar $ if v' == vb then v else v') cb))
        _ -> undefined

setIntersection :: (StringVariable v, Refreshable v, Ord v) => SetExpression v -> SetExpression v -> SetExpression v
setIntersection a0 b0 = case (toSetBuilder a0, toSetBuilder b0) of
        ss@(SetBuilder va ca, SetBuilder vb cb) ->
            let v = va `freshWRTFree` ss in  
            SetBuilder v (FOFAnd (exprCASub (\v' -> VEVar $ if v' == va then v else v') ca)
                                (exprCASub (\v' -> VEVar $ if v' == vb then v else v') cb)) 
        _ -> undefined

setDifference :: (StringVariable v, Refreshable v, Ord v) => SetExpression v -> SetExpression v -> SetExpression v
setDifference a0 b0 = case (toSetBuilder a0, toSetBuilder b0) of
        ss@(SetBuilder va ca, SetBuilder vb cb) ->
            let v = va `freshWRTFree` ss in  
            SetBuilder v (FOFAnd (exprCASub (\v' -> VEVar $ if v' == va then v else v') ca)
                                (FOFNot $ exprCASub (\v' -> VEVar $ if v' == vb then v else v') cb)) 
        _ -> undefined

data SetAssertion v = SubsetEq (SetExpression v) (SetExpression v) deriving (Eq, Ord, Functor, Foldable)

instance (ExpressionCASub SetExpression e) => ExpressionCASub SetAssertion e where
    exprCASub s (SubsetEq s1 s2) = SubsetEq (exprCASub s s1) (exprCASub s s2)
    exprCASub' s (SubsetEq s1 s2) = SubsetEq (exprCASub' s s1) (exprCASub' s s2)
    

instance Show v => Show (SetAssertion v) where
    show (SubsetEq e1 e2) = show e1 ++ " <= " ++ show e2

instance FreeVariables (SetAssertion v) v where
    foldrFree f x (SubsetEq e1 e2) = foldrFree f (foldrFree f x e2) e1

-- |'Condition's are the basic assertions and assumptions that are handled by the provers.
data Condition v = PermissionCondition (FOF PermissionAtomic v)
                | ValueCondition (FOF ValueAtomic v)
                | EqualityCondition v v
                | DisequalityCondition v v
                | SetCondition (Literal SetAssertion v)
                deriving (Eq, Ord, Functor, Foldable)


-- |The 'ConditionProp' class allows us to convert other types to 'Condition's
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

instance ConditionProp Condition where
        toCondition = id
        negativeCondition (PermissionCondition f) = PermissionCondition (FOFNot f)
        negativeCondition (ValueCondition f) = ValueCondition (FOFNot f)
        negativeCondition (EqualityCondition e1 e2) = DisequalityCondition e1 e2
        negativeCondition (DisequalityCondition e1 e2) = EqualityCondition e1 e2
        negativeCondition (SetCondition sc) = negativeCondition sc

-- |The inconsistent condition.
condFalse :: forall v. Condition v
condFalse = ValueCondition FOFFalse

condTrue :: forall v. Condition v
condTrue = ValueCondition FOFTrue

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

instance ConditionProp SetAssertion where
        toCondition = SetCondition . LPos
        negativeCondition = SetCondition . LNeg

instance ConditionProp c => ConditionProp (Literal c) where
        toCondition (LPos c) = toCondition c
        toCondition (LNeg c) = negativeCondition c
        negativeCondition (LPos c) = negativeCondition c
        negativeCondition (LNeg c) = toCondition c

-- |Generalised expressions, which can refer to permissions or to values.
data Expr v = PermissionExpr (PermissionExpression v)
        | ValueExpr (ValueExpression v)
        | VariableExpr v
        deriving (Eq, Ord, Functor, Foldable)

instance Show v => Show (Expr v) where
        show (PermissionExpr pe) = show pe
        show (ValueExpr ve) = show ve
        show (VariableExpr v) = show v


-- |Generate an equality condition for two expressions.
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

instance (Show v) => ValueExpressionCastable Expr v where
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
        exprSub _ (VEConst k) = VEConst k
        exprSub s (VEPlus e1 e2) = VEPlus (exprSub s e1) (exprSub s e2)
        exprSub s (VEMinus e1 e2) = VEMinus (exprSub s e1) (exprSub s e2)
        exprSub s (VETimes e1 e2) = VETimes (exprSub s e1) (exprSub s e2)

instance Expression Expr where
        var = VariableExpr

instance Applicative Expr where
        pure = VariableExpr
        (PermissionExpr f) <*> a = PermissionExpr $ exprSub (`fmap` a) f
        (ValueExpr f) <*> a = ValueExpr $ exprSub (`fmap` a) f
        (VariableExpr f) <*> a = fmap f a
          
-- Note, I'm slightly concerned that this might not satisfy
-- all the monad laws in some undefined cases.
instance Monad Expr where
        return = VariableExpr
        (PermissionExpr pe) >>= s = PermissionExpr $ exprSub s pe
        (ValueExpr ve) >>= s = ValueExpr $ exprSub s ve
        (VariableExpr v) >>= s = s v

instance FreeVariables (Expr v) v where
        foldrFree f x e = foldr f x e

-- |Class for things that can be converted to general expressions.
class ProverExpression c where
        toExpr :: c v -> Expr v

instance ProverExpression PermissionExpression where
        toExpr = PermissionExpr

instance ProverExpression ValueExpression where
        toExpr = ValueExpr

instance ProverExpression Identity where
        toExpr = VariableExpr . runIdentity

instance ProverExpression Expr where
        toExpr = id

-- |Cast an 'Integer' as an 'Expr'.
integerExpr :: forall v. Integer -> Expr v
integerExpr = ValueExpr . VEConst

instance FreeVariables (Condition v) v where
        foldrFree f x (PermissionCondition fof) = foldrFree f x fof
        foldrFree f x (ValueCondition fof) = foldrFree f x fof
        foldrFree f x (EqualityCondition a b) = foldr f x [a,b]
        foldrFree f x (DisequalityCondition a b) = foldr f x [a,b]
        foldrFree f x (SetCondition sc) = foldrFree f x sc
        

instance Show v => Show (Condition v) where
        show (PermissionCondition pa) = show pa
        show (ValueCondition va) = show va
        show (EqualityCondition v1 v2) = show v1 ++ " = " ++ show v2
        show (DisequalityCondition v1 v2) = show v1 ++ " != " ++ show v2
        show (SetCondition sc) = show sc

instance ExpressionCASub Condition Expr where
        exprCASub s (PermissionCondition pc) = PermissionCondition $ exprCASub s pc
        exprCASub s (ValueCondition vc) = ValueCondition $ exprCASub s vc
        exprCASub s (EqualityCondition v1 v2) = exprEquality (s v1) (s v2)
        exprCASub s (DisequalityCondition v1 v2) = negativeCondition $ exprEquality (s v1) (s v2)
        exprCASub s (SetCondition sc) = SetCondition $ exprCASub s sc
        exprCASub' s (PermissionCondition pc) = PermissionCondition $ exprCASub' s pc
        exprCASub' s (ValueCondition vc) = ValueCondition $ exprCASub' s vc
        exprCASub' s (EqualityCondition v1 v2) = exprEquality (s v1) (s v2)
        exprCASub' s (DisequalityCondition v1 v2) = negativeCondition $ exprEquality (s v1) (s v2)
        exprCASub' s (SetCondition sc) = SetCondition $ exprCASub' s sc

makeEquality :: v -> Expr v -> Condition v
-- ^Given a variable and an expression, generate a condition that
-- equates the variable with the expression
makeEquality v (PermissionExpr pe) = PermissionCondition $ FOFAtom $ PAEq (var v) pe
makeEquality v (ValueExpr ve) = ValueCondition $ FOFAtom $ VAEq (var v) ve
makeEquality v (VariableExpr ve) = EqualityCondition v ve

setAssertionToValueFOF :: (Ord v, Refreshable v) => SetAssertion v -> FOF ValueAtomic v
setAssertionToValueFOF (SubsetEq (SetSingleton e1) (SetSingleton e2)) = e1 $=$ e1
setAssertionToValueFOF (SubsetEq (SetSingleton e) (SetBuilder v a)) = exprCASub (\v' -> if v == v' then e else var v') a
setAssertionToValueFOF ss@(SubsetEq (SetBuilder v a) s2) = 
        let v0 = v `freshWRTFree` ss in
                        FOFForAll v0 $ FOFImpl (exprCASub (\v' -> if v == v' then VEVar v0 else VEVar v') a)
                                    (case s2 of
                                        SetSingleton e -> FOFAtom $ VAEq (var v0) e
                                        SetBuilder v' a' -> exprCASub (\v'' -> if v' == v'' then VEVar v0 else VEVar v'') a') 

-- |Pull out the value conditions from a list of conditions; the first argument is used to
-- determine if a given variable should be treated as a value variable.
valueConditions :: (Ord v, Refreshable v) => (v -> Bool) -> [Condition v] -> [FOF ValueAtomic v]
valueConditions tav [] = []
valueConditions tav (EqualityCondition v1 v2 : xs) =
                if tav v1 then
                        (FOFAtom $ VAEq (var v1) (var v2)) : valueConditions tav xs
                else
                        valueConditions tav xs
valueConditions tav (DisequalityCondition v1 v2 : xs) =
                if tav v1 then
                        (FOFNot $ FOFAtom $ VAEq (var v1) (var v2)) : valueConditions tav xs
                else
                        valueConditions tav xs
valueConditions tav (ValueCondition cass : xs) = cass : valueConditions tav xs
valueConditions tav (SetCondition (LPos sa) : xs) = setAssertionToValueFOF sa : valueConditions tav xs
valueConditions tav (SetCondition (LNeg sa) : xs) = FOFNot (setAssertionToValueFOF sa) : valueConditions tav xs  
valueConditions tav (_ : xs) = valueConditions tav xs

