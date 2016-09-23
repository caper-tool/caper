{-# LANGUAGE GADTs, DeriveFunctor, FlexibleInstances, MultiParamTypeClasses, RankNTypes #-}
module Caper.ProofMonad where

import Control.Applicative
import Control.Arrow
import Control.Monad
import Control.Monad.Reader.Class
import Control.Monad.State.Class

import Caper.Exceptions
import Caper.Logger

-- import Caper.Utils.MonadHoist

{-
newtype LogHandler = LogHandler ([ExceptionContext] -> LogEvent -> IO ())

data ProofResult proof state failure a =
        ProofFailure failure
        | ProofSuccess proof (IO (ProofResult proof state failure a))
        | ProofDone a (proof -> proof) state (IO (ProofResult proof state failure a))

newtype ProofM proof ctxt state failure a = ProofM {
        runProofM :: LogHandler -> ctxt -> state -> IO (ProofResult proof state failure a)
        }

combineFailure :: (Monoid failure) => failure -> ProofResult proof state failure a -> ProofResult proof state failure a
combineFailure f (ProofFailure f') = ProofFailure $! f `mappend` f'
combineFailure f (ProofSuccess p rst) = ProofSuccess p (combineFailure f <$> rst)
combineFailure f (ProofDone a pt st rst) = ProofDone a pt st (combineFailure f <$> rst)

-- catResults :: (Monoid failure) => ProofResult proof state failure a -> 

instance Monoid failure => Monad (ProofM proof ctxt state failure) where
        return r = ProofM $ \_ _ s -> return (ProofDone a id s (return $ ProofFailure mempty))
        a >>= f = ProofM $ \lh cx st -> do
                ra <- runProofM a lh cx st
                case ra of
                        ProofDone raa pft st1 rst1 -> do
                                rb <- runProofM (b raa) lh cx st1 mempty
                                case rb of
                                        ProofFailure f -> combineFailure f <$> rst1
-}


data ProverM proof ctx state failure a where
        ProofFailure :: !failure -> ProverM proof ctx state failure a
        ProofSuccess :: !proof -> ProverM proof ctx state failure a
        ProofDone :: !a -> !(proof -> proof) -> ProverM proof ctx state failure a
        ProofRead :: !(ctx -> ProverM proof ctx state failure a) -> ProverM proof ctx state failure a
        ProofState :: !(state -> (ProverM proof ctx state failure a, state)) -> ProverM proof ctx state failure a
        ProofIO :: IO (ProverM proof ctx state failure a) -> ProverM proof ctx state failure a
        ProofSubgoal :: (proof -> proof -> proof) -> (forall b. ProverM proof ctx state failure b) -> ProverM proof ctx state failure a -> ProverM proof ctx state failure a
        --ProofConjunction :: ([proof] -> proof) -> [a] -> ProverM proof ctx state failure a
        ProofChoice :: ProverM proof ctx state failure a -> ProverM proof ctx state failure a -> ProverM proof ctx state failure a
        ProofMSplit :: ProverM proof ctx state failure b ->
                (Either failure (b, ProverM proof ctx state failure b) -> ProverM proof ctx state failure a) -> ProverM proof ctx state failure a
        ProofException :: CaperException -> ProverM proof ctx state failure a
        ProofAddContext :: ExceptionContext -> ProverM proof ctx state failure b -> (b -> ProverM proof ctx state failure a) -> ProverM proof ctx state failure a
        ProofLogEventContext :: ([ExceptionContext], LogEvent) -> ProverM proof ctx state failure a -> ProverM proof ctx state failure a

instance Functor (ProverM proof ctx state failure) where
        fmap _ (ProofFailure fx) = ProofFailure fx
        fmap _ (ProofSuccess pf) = ProofSuccess pf
        fmap f (ProofDone r pt) = ProofDone (f r) pt
        fmap f (ProofRead rx) = ProofRead (fmap f . rx)
        fmap f (ProofState sx) = ProofState (first (fmap f) . sx)
        fmap f (ProofIO iox) = ProofIO (fmap (fmap f) iox)
        fmap f (ProofSubgoal ptt sp ct) = ProofSubgoal ptt sp (fmap f ct)
        fmap f (ProofChoice c1 c2) = ProofChoice (fmap f c1) (fmap f c2)
        fmap f (ProofMSplit sp ct) = ProofMSplit sp (fmap f . ct)
        fmap _ (ProofException ce) = ProofException ce
        fmap f (ProofAddContext ec l ct) = ProofAddContext ec l (fmap f . ct)
        fmap f (ProofLogEventContext le ct) = ProofLogEventContext le (fmap f ct)

(...) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(...) = (.) . (.)

transformProof :: (proof -> proof) -> ProverM proof ctx state failure a -> ProverM proof ctx state failure a
transformProof _ (ProofFailure fx) = ProofFailure fx
transformProof pt (ProofSuccess pf) = ProofSuccess (pt pf)
transformProof pt (ProofDone r pt') = ProofDone r (pt . pt')
transformProof pt (ProofRead rx) = ProofRead (transformProof pt . rx)
transformProof pt (ProofState sx) = ProofState (first (transformProof pt) . sx)
transformProof pt (ProofIO iox) = ProofIO (fmap (transformProof pt) iox)
transformProof pt (ProofSubgoal ptt sp ct) = ProofSubgoal (pt ... ptt) sp ct
transformProof pt (ProofChoice c1 c2) = ProofChoice (transformProof pt c1) (transformProof pt c2)
transformProof pt (ProofMSplit sp ct) = ProofMSplit sp (transformProof pt . ct)
transformProof _ (ProofException ce) = ProofException ce
transformProof pt (ProofAddContext ec l ct) = ProofAddContext ec l (transformProof pt . ct)
transformProof pt (ProofLogEventContext le ct) = ProofLogEventContext le (transformProof pt ct)

instance Monad (ProverM proof ctx state failure) where
        return a = ProofDone a id
        (ProofFailure fx) >>= _ = ProofFailure fx
        (ProofSuccess pf) >>= _ = ProofSuccess pf
        (ProofDone r pt) >>= ct = transformProof pt (ct r)
        (ProofRead rx) >>= ct = ProofRead (rx >=> ct)
        (ProofState sx) >>= ct = ProofState (first (>>= ct) . sx)
        (ProofIO iox) >>= ct = ProofIO (liftM (>>= ct) iox)
        (ProofSubgoal ptt sp ct0) >>= ct = ProofSubgoal ptt sp (ct0 >>= ct)
        (ProofChoice c1 c2) >>= ct = ProofChoice (c1 >>= ct) (c2 >>= ct)
        (ProofMSplit sp ct0) >>= ct = ProofMSplit sp (ct0 >=> ct)
        (ProofException ce) >>= _ = ProofException ce
        (ProofAddContext ec l ct0) >>= ct = ProofAddContext ec l (ct0 >=> ct)
        (ProofLogEventContext le ct0) >>= ct = ProofLogEventContext le (ct0 >>= ct)

instance Applicative (ProverM proof ctx state failure) where
        pure = return
        (<*>) = ap

instance Monoid failure => MonadPlus (ProverM proof ctx state failure) where
        mzero = ProofFailure mempty
        mplus = ProofChoice

instance Monoid failure => Alternative (ProverM proof ctx state failure) where
        empty = ProofFailure mempty
        (<|>) = ProofChoice

instance MonadState state (ProverM proof ctx state failure) where
        state sx = ProofState (first return . sx)

instance MonadReader ctx (ProverM proof ctx state failure) where
        ask = ProofRead return
        local _ (ProofFailure fx) = ProofFailure fx
        local _ (ProofSuccess pf) = ProofSuccess pf
        local _ (ProofDone r pt) = ProofDone r pt
        local l (ProofRead rx) = ProofRead (local l . rx . l)
        local l (ProofState sx) = ProofState (first (local l) . sx)
        local l (ProofIO iox) = ProofIO (local l <$> iox)
        local l (ProofSubgoal ptt sp ct) = ProofSubgoal ptt (local l sp) (local l ct)
        local l (ProofChoice c1 c2) = ProofChoice (local l c1) (local l c2)
        local l (ProofMSplit sp ct) = ProofMSplit (local l sp) (local l . ct)
        local _ (ProofException ce) = ProofException ce
        local l (ProofAddContext ec lo ct) = ProofAddContext ec (local l lo) (local l . ct)
        local l (ProofLogEventContext le ct) = ProofLogEventContext le (local l ct)

instance MonadRaise (ProverM proof ctx state failure) where
        raise = ProofException
        addContext ec m = ProofAddContext ec m return

instance MonadLogger (ProverM proof ctx state failure) where
        logEventContext le = ProofLogEventContext le (return ())
