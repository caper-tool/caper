{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, OverlappingInstances,
        FlexibleContexts, UndecidableInstances, Rank2Types,
        GeneralizedNewtypeDeriving
         #-}
module Caper.Logger where
import Data.Set (Set)
import qualified Data.Set
import Control.Applicative
import Control.Monad.Writer
import Control.Monad.Reader
import System.IO

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
        | WarnMissingPrecondition String String
        | WarnMissingPostcondition String String
        | WarnUninitialisedVariable String
        | WarnAmbiguousVariable Bool String
        | InfoEvent String
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
        show (WarnMissingPrecondition proc def) = "WARNING: the precondition of '" ++
                proc ++ "' is unspecified. Defaulting to '" ++ def ++ "'."
        show (WarnMissingPostcondition proc def) = "WARNING: the postcondition of '" ++
                proc ++ "' is unspecified. Defaulting to '" ++ def ++ "'."
        show (WarnUninitialisedVariable v) = "WARNING: the variable '" ++ v ++ "' is used before it is initialised."
        show (WarnAmbiguousVariable b v) = "WARNING: the variable '" ++ v ++ "' is ambiguous and could refer to a program " ++
                "variable or logical variable. It is being treated as a " ++ (if b then "program" else "logical") ++ " variable."
        show (InfoEvent s) = "INFO: " ++ s


type Log = [([ExceptionContext], LogEvent)]
type LoggerT = WriterT Log

runLoggerT :: LoggerT m a -> m (a, Log)
runLoggerT = runWriterT

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

instance (Monad m) => MonadLogger (LoggerT m) where
        logAll = tell
        logEventContext ec = tell [ec] 

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

newtype HLoggerT m a = HLoggerT (ReaderT Handle m a)
        deriving (Applicative,Monad,MonadIO,MonadHoist,Functor,Alternative,MonadPlus)

instance (MonadIO m) => MonadLogger (HLoggerT m) where
        logEventContext (ec, e) = HLoggerT $ do
                h <- ask
                liftIO $ do
                        hPrint h e  
                        mapM_ (hPutStrLn h . ("  " ++) . show) ec

runErrLogger :: HLoggerT m a -> m a
runErrLogger (HLoggerT x) = runReaderT x stderr

runOutLogger :: HLoggerT m a -> m a
runOutLogger (HLoggerT x) = runReaderT x stdout

newtype FilterLoggerT m a = FilterLoggerT (ReaderT (LogEvent -> Bool) m a)
        deriving (Applicative,Monad,MonadIO,MonadHoist,Functor,Alternative,MonadPlus)

instance (MonadLogger m) => MonadLogger (FilterLoggerT m) where
        logEventContext (ec, e) = FilterLoggerT $ do
                f <- ask
                when (f e) $ logEventContext (ec, e)

filterLogger :: (MonadLogger m) => (LogEvent -> Bool) -> FilterLoggerT m a -> m a
filterLogger f (FilterLoggerT x) = runReaderT x f

logNotProver :: LogEvent -> Bool
logNotProver (ProverInvocation {}) = False
logNotProver (ProverResult {}) = False
logNotProver _ = True 

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
