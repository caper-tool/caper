{-# LANGUAGE GADTs, DeriveFunctor, FlexibleInstances, MultiParamTypeClasses, RankNTypes #-}
module Caper.ProofMonad where

import Control.Applicative
import Control.Arrow
import Control.Monad
import Control.Monad.Reader.Class
import Control.Monad.State.Class

import Caper.Utils.NondetClasses

import Caper.Exceptions
import Caper.Logger

-- import Caper.Utils.MonadHoist

($@@) :: (a -> b -> c) -> b -> a -> c
($@@) = flip

infixl 2 $@@

($@) :: (a -> b) -> a -> b
f $@ g = f g

infix 2 $@

(...) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(...) = (.) . (.)

infixr 9 ...

newtype LogHandler = LogHandler { handleLog :: [ExceptionContext] -> LogEvent -> IO () }

data ProofResult proof state failure a =
        ProofResFailure !failure
        | ProofResSuccess !proof !(IO (ProofResult proof state failure a))
        | ProofResDone !a (proof -> proof) !state !(IO (ProofResult proof state failure a))
        | ProofResException [ExceptionContext] CaperException

combineFailure :: (Monoid failure) => failure -> ProofResult proof state failure a -> ProofResult proof state failure a
combineFailure f (ProofResFailure f') = ProofResFailure $! f `mappend` f'
combineFailure f (ProofResSuccess p rst) = ProofResSuccess p (combineFailure f <$> rst)
combineFailure f (ProofResDone a pt st rst) = ProofResDone a pt st (combineFailure f <$> rst)
combineFailure _ (ProofResException ecs ce) = ProofResException ecs ce


{-
newtype ProofM proof ctxt state failure a = ProofM {
        runProofM :: LogHandler -> ctxt -> state -> IO (ProofResult proof state failure a)
        }

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

data ProverMSplit proof ctx state failure a
        = MSplitFailure failure
        | MSplitSuccess proof (ProverM proof ctx state failure a)
        | MSplitDone a (proof -> proof) state (ProverM proof ctx state failure a)


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
                (ProverMSplit proof ctx state failure b -> ProverM proof ctx state failure a) -> ProverM proof ctx state failure a
        ProofException :: ([ExceptionContext], CaperException) -> ProverM proof ctx state failure a
        --ProofAddContext :: ExceptionContext -> ProverM proof ctx state failure b -> (b -> ProverM proof ctx state failure a) -> ProverM proof ctx state failure a
        ProofLogEventContext :: ([ExceptionContext], LogEvent) -> ProverM proof ctx state failure a -> ProverM proof ctx state failure a

reflectProofResult :: Monoid failure => IO (ProofResult proof state failure a) -> ProverM proof ctx state failure a
reflectProofResult res = ProofIO $ do
                                r <- res
                                return $ case r of
                                        ProofResFailure f -> ProofFailure f
                                        ProofResSuccess pf rst -> ProofChoice (ProofSuccess pf) (reflectProofResult rst)
                                        ProofResDone a pt st rst -> ProofChoice (ProofState $ const (ProofDone a pt, st)) (reflectProofResult rst)
                                        ProofResException ec e -> ProofException (ec, e)

combineProofResults :: Monoid failure => ProofResult proof state failure a -> IO (ProofResult proof state failure a) -> IO (ProofResult proof state failure a)
combineProofResults (ProofResFailure f) a2 = combineFailure f <$> a2
combineProofResults (ProofResSuccess p rst) a2 = return (ProofResSuccess p (rst >>= combineProofResults $@@ a2))
combineProofResults (ProofResDone a pt st rst) a2 = return (ProofResDone a pt st (rst >>= combineProofResults $@@ a2))
combineProofResults (ProofResException ecs ce) _ = return (ProofResException ecs ce)

conjoinProofResults :: Monoid failure => (proof -> proof -> proof) -> ProofResult proof state failure a -> IO (ProofResult proof state failure b) -> IO (ProofResult proof state failure b)
conjoinProofResults _ (ProofResFailure f) _ = return (ProofResFailure f)
conjoinProofResults ptt (ProofResSuccess pf1 rest1) a2 = do
                r2 <- a2
                let combineRest = combineProofResults $@@ (rest1 >>= conjoinProofResults ptt $@@ a2)
                return $ case r2 of
                        ProofResSuccess pf2 rest2 -> ProofResSuccess (ptt pf1 pf2) (rest2 >>= combineRest)
                        ProofResDone b pt st rest2 -> ProofResDone b (ptt pf1 . pt) st (rest2 >>= combineRest)
                        _ -> r2
conjoinProofResults _ (ProofResDone _ _ _ _) _ = error "conjoinProofResults: incomplete proof"
conjoinProofResults _ (ProofResException ecs ce) _ = return (ProofResException ecs ce)

transformProofs :: (proof -> proof) -> ProofResult proof state failure a -> ProofResult proof state failure a
transformProofs pt (ProofResSuccess p rst) = ProofResSuccess (pt p) (transformProofs pt <$> rst)
transformProofs pt (ProofResDone a pt' st rst) = ProofResDone a (pt . pt') st (transformProofs pt <$> rst)
transformProofs _ p = p

sequenceProofResults :: Monoid failure => ProofResult proof state failure a -> (a -> state -> IO (ProofResult proof state failure b)) -> IO (ProofResult proof state failure b)
sequenceProofResults (ProofResFailure f) _ = return (ProofResFailure f)
sequenceProofResults (ProofResSuccess pf1 rest1) c = return (ProofResSuccess pf1 (rest1 >>= sequenceProofResults $@@ c))
sequenceProofResults (ProofResDone a pt st rest1) c = do
                r2 <- c a st
                let combineRest = combineProofResults $@@ (rest1 >>= sequenceProofResults $@@ c)
                return $ case r2 of
                        ProofResSuccess pf2 rest2 -> ProofResSuccess (pt pf2) ((transformProofs pt <$> rest2) >>= combineRest)
                        ProofResDone b pt' st' rest2 -> ProofResDone b (pt . pt') st' ((transformProofs pt <$> rest2) >>= combineRest)
                        _ -> r2
sequenceProofResults (ProofResException ecs ce) _ = return (ProofResException ecs ce)


runProverM :: Monoid failure => LogHandler -> [ExceptionContext] -> ctx -> state -> ProverM proof ctx state failure a -> IO (ProofResult proof state failure a)
runProverM lh ectx ctx st (ProofFailure f) = return $ ProofResFailure f
runProverM lh ectx ctx st (ProofSuccess pf) = return $ ProofResSuccess pf (return (ProofResFailure mempty))
runProverM lh ectx ctx st (ProofDone r pt) = return $ ProofResDone r pt st (return (ProofResFailure mempty))
runProverM lh ectx ctx st (ProofRead rd) = runProverM lh ectx ctx st (rd ctx)
runProverM lh ectx ctx st (ProofState upd) = let (a, st') = upd st in runProverM lh ectx ctx st' a
runProverM lh ectx ctx st (ProofIO a) = runProverM lh ectx ctx st =<< a
runProverM lh ectx ctx st (ProofSubgoal ptt a1 a2) = do
                                r1 <- runProverM lh ectx ctx st a1
                                conjoinProofResults ptt r1 (runProverM lh ectx ctx st a2)
runProverM lh ectx ctx st (ProofChoice c1 c2) = do
                                r1 <- runProverM lh ectx ctx st c1
                                combineProofResults r1 (runProverM lh ectx ctx st c2)
runProverM lh ectx ctx st (ProofMSplit sp ct) = do
                                r1 <- runProverM lh ectx ctx st sp
                                case r1 of
                                        ProofResFailure f -> runProverM lh ectx ctx st (ct (MSplitFailure f))
                                        ProofResSuccess p rst -> runProverM lh ectx ctx st (ct (MSplitSuccess p (reflectProofResult rst)))
                                        ProofResDone a pt st' rst -> runProverM lh ectx ctx st (ct (MSplitDone a pt st' (reflectProofResult rst)))
                                        ProofResException ecs ce -> return (ProofResException ecs ce)
runProverM lh ectx ctx st (ProofException (ectx',ce)) = return $ ProofResException (ectx' ++ ectx) ce
--runProverM lh ectx ctx st (ProofAddContext ec lwc ct) = runProverM lh (ec : ectx) ctx st lwc >>= sequenceProofResults $@@ (flip (runProverM lh ectx ctx) . ct)
runProverM lh ectx ctx st (ProofLogEventContext (lectx, le) ct) = handleLog lh (lectx ++ ectx) le >> runProverM lh ectx ctx st ct

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
        --fmap f (ProofAddContext ec l ct) = ProofAddContext ec l (fmap f . ct)
        fmap f (ProofLogEventContext le ct) = ProofLogEventContext le (fmap f ct)


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
--transformProof pt (ProofAddContext ec l ct) = ProofAddContext ec l (transformProof pt . ct)
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
        --(ProofAddContext ec l ct0) >>= ct = ProofAddContext ec l (ct0 >=> ct)
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
        --local l (ProofAddContext ec lo ct) = ProofAddContext ec (local l lo) (local l . ct)
        local l (ProofLogEventContext le ct) = ProofLogEventContext le (local l ct)

instance MonadRaise (ProverM proof ctx state failure) where
        raise ex = ProofException ([], ex)
        --addContext ec m = ProofAddContext ec m return
        addContext _ (ProofFailure fx) = ProofFailure fx
        addContext _ (ProofSuccess pf) = ProofSuccess pf
        addContext _ (ProofDone r pt) = ProofDone r pt
        addContext ec (ProofRead rx) = ProofRead (addContext ec . rx)
        addContext ec (ProofState sx) = ProofState (first (addContext ec) . sx)
        addContext ec (ProofIO iox) = ProofIO (addContext ec <$> iox)
        addContext ec (ProofSubgoal ptt sp ct) = ProofSubgoal ptt (addContext ec sp) (addContext ec ct)
        addContext ec (ProofChoice c1 c2) = ProofChoice (addContext ec c1) (addContext ec c2)
        addContext ec (ProofMSplit sp ct) = ProofMSplit (addContext ec sp) (addContext ec . ct)
        addContext ec (ProofException (ecs, ce)) = ProofException (ec : ecs, ce)
        --addContext ec (ProofAddContext ec lo ct) = ProofAddContext ec (addContext ec lo) (addContext ec . ct)
        addContext ec (ProofLogEventContext (ecs, le) ct) = ProofLogEventContext (ec : ecs, le) (addContext ec ct)


instance MonadLogger (ProverM proof ctx state failure) where
        logEventContext le = ProofLogEventContext le (return ())

instance Monoid failure => MonadOrElse (ProverM proof ctx state failure) where
        a `orElse` b = do
                r <- ProofMSplit a return
                case r of
                        MSplitFailure f -> b -- /Could/ recall the failure rather than discarding it
                        MSplitSuccess p rst -> ProofSuccess p `mplus` rst
                        MSplitDone res pt st rst -> ProofState (const (ProofDone res pt, st)) `mplus` rst
