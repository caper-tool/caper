module Caper.Provers.Values.SBV where
import Data.SBV
import Prelude hiding (sequence,foldl,mapM_,mapM)
import Data.Foldable
import Data.Traversable
import Control.Monad hiding (mapM, mapM_)

import Caper.ProverDatatypes
import Caper.FirstOrder

toSInteger :: (v -> SInteger) -> ValueExpression v -> SInteger
toSInteger s (VEConst i) = fromInteger i
toSInteger s (VEVar v) = s v
toSInteger s (VEPlus e1 e2) = toSInteger s e1 + toSInteger s e2
toSInteger s (VEMinus e1 e2) = toSInteger s e1 - toSInteger s e2
toSInteger s (VETimes e1 e2) = toSInteger s e1 * toSInteger s e2

atomToSBool :: (v -> SInteger) -> ValueAtomic v -> SBool
atomToSBool s (VAEq e1 e2) = toSInteger s e1 .== toSInteger s e2
atomToSBool s (VALt e1 e2) = toSInteger s e1 .< toSInteger s e2

toSBool :: (Show v, Eq v) => (v -> SInteger) -> FOF ValueAtomic v -> SBool
toSBool s (FOFAtom a) = atomToSBool s a
toSBool s (FOFAnd f1 f2) = toSBool s f1 &&& toSBool s f2
toSBool s (FOFOr f1 f2) = toSBool s f1 ||| toSBool s f2
toSBool s (FOFImpl f1 f2) = toSBool s f1 ==> toSBool s f2
toSBool s (FOFNot f) = bnot $ toSBool s f
toSBool s (FOFFalse) = false
toSBool s (FOFTrue) = true
toSBool _ _ = error "toSBool: can only be applied to quantifier-free formulae."

toPredicate :: (Show v, Eq v, Refreshable v) => (v -> SInteger) -> FOF ValueAtomic v -> Predicate
toPredicate s0 = toPredicate' s0 . pNormalise
        where
                toPredicate' s (FOFForAll v f) = forAll [show v]
                    (\si -> toPredicate' (\w -> if w == v then si else s w) f)  
                toPredicate' s (FOFExists v f) = forSome [show v]
                    (\si -> toPredicate' (\w -> if w == v then si else s w) f)
                toPredicate' s f = return $ toSBool s f  

valueCheck :: (Eq v, Show v, Refreshable v) => Maybe Int -> FOF ValueAtomic v -> IO (Maybe Bool)
valueCheck timeout f = do
        putStrLn (show f) 
        isTheorem timeout $ toPredicate (\v -> error $ "Unquantified variable " ++ show v ++ " in formula:\n" ++ show f) f

valueProverInfo :: IO String
valueProverInfo =
        return $ "SBV library, configuration: " ++ show sbvCurrentSolver
