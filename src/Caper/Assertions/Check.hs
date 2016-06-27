{-# LANGUAGE MultiParamTypeClasses #-}
module Caper.Assertions.Check where

import Control.Monad.State hiding (state)
import Control.Monad.Reader

import Caper.Exceptions
import Caper.ProverDatatypes
import Caper.Prover
import Caper.RegionTypes
import Caper.Parser.AST
import Caper.Parser.AST.SourcePos

-- |Check that the list of parameters for a region is of the right length and
-- that each parameter is of the appropriate type.
-- For this, the region identifier is not treated as a parameter, and the
-- state is not considered to be a parameter.
checkRegionParams :: (MonadState s m, AssumptionLenses s,
                MonadReader r m, RTCGetter r,
                MonadRaise m) =>
        RTId -> [(Expr VariableID, AnyExpr)] -> m ()
checkRegionParams rtid params = do
                        rt <- lookupRType rtid
                        let types = map snd $ tail $ rtParameters rt
                        if length types == length params then
                                checkParams (2 :: Int) params types
                            else
                                raise $ ArgumentCountMismatch (2 + length types) (2 + length params)
        where
                checkParams n ((e, p) : ps) (t : ts) = do
                        addContext (DescriptiveContext (sourcePos p) $
                                        "In argument " ++ show n) $
                                checkExpressionAtTypeE e t
                        checkParams (n+1) ps ts
                checkParams _ _ _ = return ()

-- |Determine if an assertion is stable by a straight-forward syntactic check.
-- This allows us to short-circuit more complex stability testing where it is
-- not necessary.  If this procedure returns 'True', the assertion is guaranteed
-- to be stable.
--
-- Currently, this simply checks that no regions are mentioned
isTriviallyStable :: Assrt -> Bool
isTriviallyStable AssrtPure{} = True
isTriviallyStable (AssrtSpatial _ (SARegion _)) = False
isTriviallyStable (AssrtSpatial _ _) = True
isTriviallyStable (AssrtConj _ a1 a2) = isTriviallyStable a1 && isTriviallyStable a2
isTriviallyStable (AssrtITE _ _ a1 a2) = isTriviallyStable a1 && isTriviallyStable a2
isTriviallyStable (AssrtOr _ a1 a2) = isTriviallyStable a1 && isTriviallyStable a2
