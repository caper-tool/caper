module Caper.TransitivityCheck where

import Control.Monad.Trans.State
import Control.Monad.Trans
import Control.Monad

import Caper.ProverDatatypes
import Caper.ProverStates
import Caper.Prover
import Caper.RegionTypes

-- Probably I should put this back in RegionTypes.

checkForClosure :: (MonadIO m, MonadPlus m) => RegionType -> TransitionRule -> TransitionRule -> m ()
checkForClosure rt tr1 tr2 = flip evalStateT (emptyAssumptions) $ do
        undefined
 