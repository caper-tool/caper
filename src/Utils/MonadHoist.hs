{-# LANGUAGE Rank2Types #-}
{- |The MonadHoist module provides a class for monad transformers that
   are functors on the category of monads.  That is, they provide a
   function 'hoist' that lifts a mapping between monads to a mapping
   between the transformed monads.
 -}
module Utils.MonadHoist where
import Control.Monad.Reader
import Control.Monad.Error
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.RWS
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Either

-- |Monad transformers implementing 'MonadHoist' should satisfy the
-- following law:
--
-- @
--      lift . f = hoist f . lift
-- @
class MonadHoist t where
        hoist :: (Monad n, Monad m) => (forall a. n a -> m a) -> t n a -> t m a

instance MonadHoist (ReaderT r) where
        hoist f a = ReaderT $ f . runReaderT a

instance MonadHoist (ErrorT e) where
        hoist f = ErrorT . f . runErrorT

instance MonadHoist (StateT s) where
        hoist f = mapStateT f -- StateT $ f . runStateT a

instance MonadHoist (WriterT w) where
        hoist f = WriterT . f . runWriterT

instance MonadHoist (RWST r w s) where
        hoist f a = RWST $ \r s -> f $ runRWST a r s

instance MonadHoist MaybeT where
        hoist f = MaybeT . f . runMaybeT

instance MonadHoist (EitherT e) where
        hoist f = EitherT . f . runEitherT
