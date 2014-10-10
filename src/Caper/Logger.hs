{-# LANGUAGE FlexibleInstances, OverlappingInstances,
        FlexibleContexts, UndecidableInstances, Rank2Types,
        GeneralizedNewtypeDeriving
         #-}
module Caper.Logger where
import Data.Set (Set)
import qualified Data.Set
import Control.Monad.Writer
import Control.Monad.Reader

import Caper.Utils.MonadHoist
import Caper.ProverDatatypes
import Caper.ExceptionContext

data ProverType = PermissionProverType | ValueProverType

instance Show ProverType where
        show PermissionProverType = "permissions prover"
        show ValueProverType = "value prover"

data LogEvent
        = WarnAutoBind (Set VariableID)
        | WarnUnconstrainedParameter String VariableType
        | ProverInvocation ProverType String
        | ProverResult (Maybe Bool)
instance Show LogEvent where
        show (WarnAutoBind vars) = "WARNING: the variables " ++ show (Data.Set.toList vars) ++
                " are being automatically bound as existentials."
        show (WarnUnconstrainedParameter param typ) = 
                "WARNING: The type of parameter '" ++ param ++
                "' could not be inferred. Assuming type '" ++ show typ ++
                "'."
        show (ProverInvocation pt assrt) = "PROVER: invoking " ++ show pt ++
                " on:\n" ++ assrt
        show (ProverResult res) = "PROVER: " ++ case res of
                        Just True -> "proved"
                        Just False -> "disproved"
                        Nothing -> "no answer"
                

type Log = [([ExceptionContext], LogEvent)]
--type LoggerT = WriterT Log
newtype LoggerT m a = LoggerT (WriterT Log m a) deriving (Monad,MonadHoist,MonadIO)

runLoggerT :: LoggerT m a -> m (a, Log)
runLoggerT (LoggerT w) = runWriterT w

class Monad m => MonadLogger m where
        logAll :: Log -> m ()
        logAll = mapM_ logEventContext
        logEventContext :: ([ExceptionContext], LogEvent) -> m ()
        logEventContext = logAll . (:[]) 
        logEvent :: LogEvent -> m ()
        logEvent e = logEventContext ([],e)

joinLoggerT :: MonadLogger m => LoggerT m a -> m a
joinLoggerT x = do
                (res, lg) <- runLoggerT x
                logAll lg
                return res

liftLoggerT :: (Monad n, MonadLogger m) =>
        (forall b. n b -> m b) -> LoggerT n a -> m a
liftLoggerT f = joinLoggerT . hoist f



instance (MonadTrans t, Monad (t m), MonadLogger m) => MonadLogger (t m) where
        logAll = lift . logAll
        logEventContext = lift . logEventContext
        logEvent = lift . logEvent

instance (MonadLogger m) => MonadLogger (ReaderT [ExceptionContext] m) where
        logAll l = do
                ctx <- ask
                lift $ logAll [(ec ++ ctx, e) | (ec, e) <- l]
        logEventContext (ec,e) = do
                ctx <- ask
                lift $ logEventContext (ec ++ ctx, e)

instance (Monad m) => MonadLogger (LoggerT m) where
        logAll = LoggerT . tell
        logEventContext ec = logAll [ec] 


{-

test0 :: (MonadIO m, MonadLogger m, MonadRaise m) => m ()
test0 = addContext (StringContext "Here") $ do
        liftIO $ putStrLn "bar"
        logEvent (WarnAutoBind Data.Set.empty)
        raise $ SyntaxNotImplemented "foo"

test :: IO (Either ([ExceptionContext], CaperException) () , [([ExceptionContext], LogEvent)])                
test = runWriterT $ runRaiseT $ addContext (StringContext "Here") (liftIO (putStrLn "bar") >> logEvent (WarnAutoBind Data.Set.empty) >> (raise $ SyntaxNotImplemented "foo"))

runStuff :: (MonadIO m) => RaiseT (LoggerT m) a -> m a
runStuff a = do
        (r, w) <- runWriterT $ runRaiseT a
        liftIO $ mapM_ (print) w
        return $! either (error . show) id r
  -}    