module Caper.Utils.Alternating where

import Control.Monad hiding (sequence)
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Control.Monad.Reader
import Debug.Trace

import Caper.Utils.NondetClasses
import Caper.Utils.MonadHoist

{-

data Alternating s m a = Alternating
{--
          Angelic (Alternating s m a) (Alternating s m a)
        | Failure
        | Demonic (Alternating s m a) (Alternating s m a)
        | Success
   --}
   
instance Functor m => Functor s m where

instance Monad m => Monad s m where

abstract :: (s -> s -> Maybe s) -> Alternating s m a     
-}