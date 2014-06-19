{- Regions -}
module Regions where
import Control.Monad.State hiding (mapM_,mapM)

import RegionTypes
import AliasingMap
import ProverDatatypes
import Prover -- TODO: move some stuff from Prover to ProverDatatypes?
import Guards


data RegionInstance = RegionInstance {
        riType :: RTId,
        riParameters :: [Expr VariableID]
}

data Region = Region {
        regDirty :: Bool,
        regTypeInstance :: Maybe RegionInstance,
        regState :: Maybe (ValueExpression VariableID),
        regGuards :: Guard VariableID
}

-- TODO: possibly move somewhere more relevant
mergeMaybe :: (Monad m) => (a -> a -> m a) -> Maybe a -> Maybe a -> m (Maybe a)
mergeMaybe _ Nothing m2 = return m2
mergeMaybe _ m1 Nothing = return m1
mergeMaybe op (Just m1) (Just m2) = op m1 m2 >>= return . Just

-- Merge region instances, adding equality assumptions between parameters
-- Pre: region instances should be checked against their types; i.e.
-- if they have the same region type, then they must have the same number
-- and type of parameters.
mergeRegionInstances :: (MonadState s m, AssumptionLenses s) => RegionInstance -> RegionInstance -> m (RegionInstance)
mergeRegionInstances i1@(RegionInstance t1 ps1) i2@(RegionInstance t2 ps2)
        = (if t1 /= t2 then
                -- These regions cannot be the same, so assume false!
                assume condFalse
          else forM_ (zip ps1 ps2) $ \(p1, p2) ->
                        -- The precondition should guarantee against an error
                        -- in exprEquality.
                        assume $ exprEquality p1 p2)
          >> return i1

mergeValueExpressions :: (MonadState s m, AssumptionLenses s) =>
        ValueExpression VariableID ->
        ValueExpression VariableID -> m (ValueExpression VariableID)
mergeValueExpressions ve1 ve2 = (assumeTrue $ ve1 $=$ ve2) >> return ve1
