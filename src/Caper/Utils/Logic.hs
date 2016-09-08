{-# LANGUAGE RankNTypes, FlexibleInstances, MultiParamTypeClasses #-}
-- | An implementation of a non-determism monad inspired by
-- <http://dl.acm.org/citation.cfm?id=1086390 Oleg et al. 2005>.
module Caper.Utils.Logic where

import Control.Applicative
import Control.Monad
import Control.Monad.Cont
import Control.Monad.Trans
import Data.Monoid

import Caper.Utils.Failure
import Caper.Utils.NondetClasses

type FailContinuation ans flr = flr -> ans
type SucceedContinuation ans flr a = a -> FailContinuation ans flr -> ans

newtype SFContT flr m a =
        SFKT {
                unSFKT :: forall ans. SucceedContinuation (m ans) flr a -> FailContinuation (m ans) flr -> m ans
        }

instance Functor (SFContT flr m) where
        fmap f m = SFKT $ \sk -> unSFKT m (sk . f)

instance {-Monad m =>-} Monad (SFContT flr m) where
        return e = SFKT $ \sk fk -> sk e fk
        m >>= f = SFKT $ \sk -> unSFKT m $ \a -> unSFKT (f a) sk

instance {-Monad m =>-} Applicative (SFContT flr m) where
        pure = return
        x <*> y = x `ap` y

instance Monoid flr => MonadPlus (SFContT flr m) where
        mzero = SFKT $ \sk fk -> fk mempty
        m1 `mplus` m2 = SFKT $ \sk fk -> unSFKT m1 sk (\f1 -> unSFKT m2 sk (\f2 -> fk $! f1 <> f2))

instance Monoid flr => Alternative (SFContT flr m) where
        empty = mzero
        (<|>) = mplus

instance MonadTrans (SFContT flr) where
        lift m = SFKT $ \sk fk -> m >>= \a -> sk a fk

{-
instance MonadHoist (SFContT flr) where
        hoist h n = SFKT $ \sk fk -> 
-}

instance Failure f (SFContT f m) where
        failure f = SFKT $ \sk fk -> fk f

class LogicT t where
        -- |Deconstruct the head of the result stream
        msplit :: (Monad m, Monoid f) => t f m a -> t f m (Either f (a, t f m a))
        -- |Fair disjunction
        interleave :: (MonadPlus (t f m), Failure f (t f m), Monad m, Monoid f) => t f m a -> t f m a -> t f m a
        interleave a b = do
                        r <- msplit a
                        case r of
                                Left f -> failure f `mplus` b
                                Right (hd, rst) -> return hd `mplus` interleave b rst
        -- |Fair conjunction
        (>>-) :: (MonadPlus (t f m), Failure f (t f m), Monad m, Monoid f) => t f m a -> (a -> t f m b) -> t f m b
        a >>- k = do
                r <- msplit a
                case r of
                        Left f -> failure f
                        Right (hd, rst) -> interleave (k hd) (rst >>- k)
        -- |If-then-else (soft-cut)
        ifte :: (MonadPlus (t f m), Failure f (t f m), Monad m, Monoid f) => t f m a -> (a -> t f m b) -> (f -> t f m b) -> t f m b
        ifte a thn els = do
                r <- msplit a
                case r of
                        Left f -> els f
                        Right (hd, rst) -> thn hd `mplus` (rst >>= thn)
        -- |Pruning (don't-care nondeterminism)
        once :: (MonadPlus (t f m), Failure f (t f m), Monad m, Monoid f) => t f m a -> t f m a
        once a = do
                r <- msplit a
                case r of
                        Left f -> failure f
                        Right (hd, _) -> return hd

reflect :: (MonadPlus m, Failure f m) => Either f (a, m a) -> m a
reflect (Left f) = failure f
reflect (Right (a, rest)) = return a `mplus` rest

instance LogicT SFContT where
        msplit tma = lift (unSFKT tma ssk (return . Left))
                where
                        ssk a fk = return (Right (a, (lift (fk mempty) >>= reflect)))

instance (Monad m, Monoid f) => MonadOrElse (SFContT f m) where
        a `orElse` b = ifte a return (const b)


{-
instance (Monad m, Monoid f) => OnFailure f (ContT r (SFContT f m)) where
        retry = -}
