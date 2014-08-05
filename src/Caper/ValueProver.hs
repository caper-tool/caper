module Caper.ValueProver where
import Data.SBV
import Prelude hiding (sequence,foldl,mapM_,mapM)
import Data.Foldable
import Data.Traversable
import Control.Monad hiding (mapM, mapM_)

import Caper.ProverDatatypes

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

valueCheck :: (Eq v, Show v) => Maybe Int -> FOF ValueAtomic v -> IO (Maybe Bool)
valueCheck timeout f = isTheorem timeout $ toPredicate (\v -> error $ "Unquantified variable " ++ show v ++ " in formula:\n" ++ show f) f

valueProverInfo :: IO String
valueProverInfo =
        return $ "SBV library, configuration: " ++ show sbvCurrentSolver
