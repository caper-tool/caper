module Transitions where
import ProverDatatypes
import Prover

data ClosureVariable v = Context v | Local String deriving (Eq, Ord)

instance (Show v) => Show (ClosureVariable v) where
        show (Context v) = "c_" ++ (show v)
        show (Local s) = "l_" ++ s

instance (StringVariable v) => StringVariable (ClosureVariable v) where
        varToString (Context v) = "c_" ++ (varToString v)
        varToString (Local s) = "l_" ++ s

-- ssLowerBound and ssUpperBound are the (inclusive) lower
-- and upper bounds of the state space.
-- invariant: ssLowerBound <= ssUpperBound (if both are not Nothing)
data StateSpace = StateSpace {
                ssLowerBound :: Maybe Integer,
                ssUpperBound :: Maybe Integer
                }
isFinite :: StateSpace -> Bool
isFinite (StateSpace (Just _) (Just _)) = True
isFinite _ = False

ssSize :: StateSpace -> Maybe Integer
ssSize (StateSpace (Just x) (Just y)) = y - x + 1


