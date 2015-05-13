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
checkRegionParams :: (MonadState s m, AssumptionLenses s,
                MonadReader r m, RTCGetter r,
                MonadRaise m) =>
        RTId -> [(Expr VariableID, AnyExpr)] -> m ()
checkRegionParams rtid params = do
                        rt <- lookupRType rtid
                        let types = map snd $ rtParameters rt
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


