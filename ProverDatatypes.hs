{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module ProverDatatypes where
import Prelude hiding (sequence,foldl,foldr,elem,mapM_,mapM)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.State hiding (mapM_,mapM)
import Data.Foldable
import Data.Traversable
import Data.Typeable
import Control.Monad hiding (mapM_,mapM)



data VariableID = VIDNamed () String
                | VIDInternal () String
                deriving (Eq,Ord,Typeable)

instance Show VariableID where
        show (VIDNamed _ s) = s
        show (VIDInternal _ s) = "__" ++ s

vidToString :: VariableID -> String
vidToString (VIDNamed _ n) = "n_" ++ n
vidToString (VIDInternal _ n) = "i_" ++ n

data EVariable = EVNormal VariableID | EVExistential () String -- | EVInternal () Int
        deriving (Eq, Ord, Typeable)

instance Show EVariable where
        show (EVNormal v) = show v
        show (EVExistential _ s) = "?" ++ s
--        show (EVInternal _ n) = "?_" ++ show n

evarToString :: EVariable -> String
evarToString (EVExistential _ n) = "e_" ++ n
evarToString (EVNormal v) = vidToString v


data Literal a v = LPos (a v) | LNeg (a v) deriving (Functor, Foldable, Traversable)

instance Show (a v) => Show (Literal a v) where
        show (LPos x) = show x
        show (LNeg x) = "¬ " ++ show x

data PermissionExpression v = PEFull
                        | PEZero
                        | PEVar v
                        | PESum (PermissionExpression v) (PermissionExpression v)
                        | PECompl (PermissionExpression v)
                        deriving (Eq,Ord,Functor, Foldable, Traversable)
instance Show v => Show (PermissionExpression v) where
        show PEFull = "1"
        show PEZero = "0"
        show (PESum e1 e2) = "(" ++ show e1 ++ " + " ++ show e2 ++ ")"
        show (PECompl e) = "(1 - " ++ show e ++ ")"
        show (PEVar v) = show v

instance Monad PermissionExpression where
        return = PEVar
        (PEVar v) >>= b = b v
        PESum x y >>= b = PESum (x >>= b) (y >>= b)
        PECompl e >>= b = PECompl (e >>= b)
        PEFull >>= _ = PEFull
        PEZero >>= _ = PEZero

class Expression e where
        var :: v -> e v

instance Expression PermissionExpression where
        var = PEVar

data PermissionAtomic v =
                 PAEq (PermissionExpression v) (PermissionExpression v)
                | PADis (PermissionExpression v) (PermissionExpression v)
                deriving (Functor, Foldable, Traversable, Eq, Ord)

class ExpressionSub c e where
        exprSub :: (v -> e w) -> c v -> c w

instance Monad m => ExpressionSub m m where
        exprSub a b = b >>= a

instance ExpressionSub PermissionAtomic PermissionExpression where
        exprSub s (PAEq x y) = PAEq (exprSub s x) (exprSub s y)
        exprSub s (PADis x y) = PADis (exprSub s x) (exprSub s y)

instance Show v => Show (PermissionAtomic v) where
        show (PAEq v1 v2) = show v1 ++ " =p= " ++ show v2
        show (PADis v1 v2) = show v1 ++ " # " ++ show v2

type VIDPermissionAtomic = PermissionAtomic VariableID

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

instance Show a => Show (ValueExpression a) where
        show (VEConst n) = show n
        show (VEVar v) = show v
        show (VEPlus e1 e2) = "(" ++ show e1 ++ " + " ++ show e2 ++  ")"
        show (VEMinus e1 e2) = "(" ++ show e1 ++ " - " ++ show e2 ++  ")"
        show (VETimes e1 e2) = "(" ++ show e1 ++ " * " ++ show e2 ++  ")"

data ValueAtomic v =
          VAEq (ValueExpression v) (ValueExpression v)
        | VALt (ValueExpression v) (ValueExpression v)
        deriving (Eq,Ord,Functor,Foldable,Traversable)

instance Show a => Show (ValueAtomic a) where
        show (VAEq e1 e2) = show e1 ++ " =v= " ++ show e2
        show (VALt e1 e2) = show e1 ++ " < " ++ show e2



data VariableType = VTPermission | VTValue
        deriving (Eq, Ord, Typeable)

data Provers = Provers {
                permissionsProver :: FOF PermissionAtomic String -> IO (Maybe Bool),
                valueProver :: FOF ValueAtomic String -> IO (Maybe Bool)
                }

instance Show VariableType where
        show VTPermission = "Permission"
        show VTValue = "Value"

data Assertion = PermissionAssertion (Literal PermissionAtomic VariableID)

instance Show Assertion where
        show (PermissionAssertion pa) = show pa




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
        show (FOFNot f) = "¬ " ++ show f
        show (FOFAnd f1 f2) = "(" ++ show f1 ++ " /\\ " ++ show f2 ++ ")"
        show (FOFOr f1 f2) = "(" ++ show f1 ++ " \\/ " ++ show f2 ++ ")"
        show (FOFImpl f1 f2) = "(" ++ show f1 ++ " => " ++ show f2 ++ ")"
        show (FOFForAll v f1) = "![" ++ show v ++ "](" ++ show f1 ++ ")"
        show (FOFExists v f1) = "?[" ++ show v ++ "](" ++ show f1 ++ ")"

class FreeVariables f where
        foldrFree :: (Eq a) => (a -> b -> b) -> b -> f a -> b
        freeIn :: (Eq v) => v -> f v -> Bool
        freeIn v = foldrFree ( (||) . (== v) ) False
        freeVariables :: (Ord v) => f v -> Set.Set v
        freeVariables = foldrFree Set.insert Set.empty

instance (Foldable a) => FreeVariables (FOF a) where
        foldrFree f = ff []
                where
                        ff bound x (FOFForAll v s) = ff (v : bound) x s
                        ff bound x (FOFExists v s) = ff (v : bound) x s
                        ff bound x (FOFAtom a) = foldr (ignoring bound) x a
                        ff bound x (FOFAnd f1 f2) = ff bound (ff bound x f2) f1
                        ff bound x (FOFOr f1 f2) = ff bound (ff bound x f2) f1
                        ff bound x (FOFImpl f1 f2) = ff bound (ff bound x f2) f1
                        ff bound x (FOFNot f') = ff bound x f'
                        ff bound x _ = x
                        ignoring l u v = if u `elem` l then v else f u v

literalToFOF :: Literal a v -> FOF a v
literalToFOF (LPos a) = FOFAtom a
literalToFOF (LNeg a) = FOFNot $ FOFAtom a
