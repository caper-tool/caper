{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module ValueProver where
import Data.SBV
import ProverDatatypes
import Prelude hiding (sequence,foldl,mapM_,mapM)
import Data.Foldable
import Data.Traversable
import Control.Monad hiding (mapM, mapM_)

data ValueExpression v =
          VEConst Integer
        | VEVar v
        | VEPlus (ValueExpression v) (ValueExpression v)
        | VEMinus (ValueExpression v) (ValueExpression v)
        | VETimes (ValueExpression v) (ValueExpression v)
        deriving (Eq,Ord,Functor,Foldable,Traversable)

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

toSInteger :: (v -> SInteger) -> ValueExpression v -> SInteger
toSInteger s (VEConst i) = fromInteger i
toSInteger s (VEVar v) = s v
toSInteger s (VEPlus e1 e2) = toSInteger s e1 + toSInteger s e2
toSInteger s (VEMinus e1 e2) = toSInteger s e1 - toSInteger s e2
toSInteger s (VETimes e1 e2) = toSInteger s e1 * toSInteger s e2

atomToSBool :: (v -> SInteger) -> ValueAtomic v -> SBool
atomToSBool s (VAEq e1 e2) = toSInteger s e1 .== toSInteger s e2
atomToSBool s (VALt e1 e2) = toSInteger s e1 .< toSInteger s e2

toPredicate :: (Show v, Eq v) => (v -> SInteger) -> FOF ValueAtomic v -> Predicate
toPredicate s (FOFForAll v f) = forAll [show v] (\si -> toPredicate (\w -> if w == v then si else s w) f)
toPredicate s (FOFExists v f) = forSome [show v] (\si -> toPredicate (\w -> if w == v then si else s w) f)
toPredicate s (FOFAtom a) = return $ atomToSBool s a
toPredicate s (FOFAnd f1 f2) = do
                               p1 <- toPredicate s f1
                               p2 <- toPredicate s f2
                               return $ p1 &&& p2
toPredicate s (FOFOr f1 f2) = do
                               p1 <- toPredicate s f1
                               p2 <- toPredicate s f2
                               return $ p1 ||| p2
toPredicate s (FOFImpl f1 f2) = do
                               p1 <- toPredicate s f1
                               p2 <- toPredicate s f2
                               return $ p1 ==> p2
toPredicate s (FOFNot f1) = do
                               p1 <- toPredicate s f1
                               return $ bnot p1
toPredicate s (FOFFalse) = return false
toPredicate s (FOFTrue) = return true

valueCheck :: (Eq v, Show v) => FOF ValueAtomic v -> IO (Maybe Bool)
valueCheck f = isTheorem Nothing $ toPredicate (\v -> error $ "Unquantified variable " ++ show v ++ " in formula:\n" ++ show f) f
