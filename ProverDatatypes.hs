{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
module ProverDatatypes where
import Prelude hiding (sequence,foldl,mapM_,mapM)
import qualified Data.Map as Map
import Control.Monad.State hiding (mapM_,mapM)
import Data.Foldable
import Data.Traversable
import Data.Typeable
import Control.Monad hiding (mapM_,mapM)

data VariableType = VTPermission
        deriving (Eq, Ord, Show)

data VariableID = VIDNamed () String
                | VIDInternal () String
                deriving (Eq,Ord,Typeable)

instance Show VariableID where
        show (VIDNamed _ s) = s
        show (VIDInternal _ s) = "__" ++ s


data EVariable = EVNormal VariableID | EVExistential () String -- | EVInternal () Int
        deriving (Eq, Ord, Typeable)

instance Show EVariable where
        show (EVNormal v) = show v
        show (EVExistential _ s) = "?" ++ s
--        show (EVInternal _ n) = "?_" ++ show n

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

data PermissionAtomic v =
                 PAEq (PermissionExpression v) (PermissionExpression v)
                | PADis (PermissionExpression v) (PermissionExpression v)
                deriving (Functor, Foldable, Traversable)

class PermExprSubable c where
        permExprSub :: (v -> PermissionExpression w) -> c v -> c w

instance PermExprSubable PermissionExpression where
        permExprSub a b = b >>= a

instance PermExprSubable PermissionAtomic where
        permExprSub s (PAEq x y) = PAEq (permExprSub s x) (permExprSub s y)
        permExprSub s (PADis x y) = PADis (permExprSub s x) (permExprSub s y)

instance Show v => Show (PermissionAtomic v) where
        show (PAEq v1 v2) = show v1 ++ " =p= " ++ show v2
        show (PADis v1 v2) = show v1 ++ " # " ++ show v2

type VIDPermissionAtomic = PermissionAtomic VariableID

type PermissionLiteral = Literal PermissionAtomic

instance PermExprSubable (Literal PermissionAtomic) where
        permExprSub s (LPos a) = LPos (permExprSub s a)
        permExprSub s (LNeg a) = LNeg (permExprSub s a)


data Assertion = PermissionAssertion (Literal PermissionAtomic VariableID)

instance Show Assertion where
        show (PermissionAssertion pa) = show pa

data Context = Context {
        bindings :: Map.Map VariableID VariableType,
        assertions :: [Assertion]
        }

instance Show Context where
        show (Context _ as) = foldl (++) "" $ map (('\n':) . show) as

emptyContext :: Context
-- A context with no variables and no assertions
emptyContext = Context Map.empty []

type ProverT = StateT Context

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

literalToFOF :: Literal a v -> FOF a v
literalToFOF (LPos a) = FOFAtom a
literalToFOF (LNeg a) = FOFNot $ FOFAtom a
