{-# LANGUAGE DeriveFunctor, DeriveTraversable, DeriveFoldable #-}
import Data.Foldable
import Data.Traversable
import FirstOrder
import qualified Data.Map as Map
import qualified Data.Set as Set

data PresExpression v = PresExpr (Map.Map v Integer) Integer deriving (Eq,Ord)

instance (Show v) => Show (PresExpression v) where
        show (PresExpr m n) = Map.foldWithKey (\k a b -> show a ++ show k ++ " + " ++ b) (show n) m

presZero :: PresExpression v
presZero = PresExpr (Map.empty) 0

presAdd :: (Eq v, Ord v) => PresExpression v -> PresExpression v -> PresExpression v
presAdd (PresExpr m1 n1) (PresExpr m2 n2) = PresExpr (Map.unionWith (+) m1 m2) (n1 + n2)

presNeg :: (Eq v, Ord v) => PresExpression v -> PresExpression v
presNeg (PresExpr m n) = PresExpr (Map.map negate m) (negate n)

presSub :: (Eq v, Ord v) => PresExpression v -> PresExpression v -> PresExpression v
presSub pe1 pe2 = presAdd pe1 (presNeg pe2)

presMult :: (Eq v, Ord v) => Integer -> PresExpression v -> PresExpression v
presMult t (PresExpr m n) = PresExpr (Map.map (t*) m) (t * n)



