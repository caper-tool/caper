{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, UndecidableInstances, OverlappingInstances, TypeSynonymInstances, FlexibleContexts #-}
{- |Infrastructure for tests. -}
module Infrastructure where
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Either

import Caper.Utils.MonadHoist

import Caper.ProverDatatypes
import Caper.Prover
import Caper.Provers
import Caper.SymbolicState
import Caper.Utils.Choice
import Caper.Logger
import Caper.RegionTypes
import Caper.Exceptions
import Caper.Assertions
import Caper.Parser.AST.Annotation
import Caper.Contexts

import RegionTypes

import Text.Parsec.Pos

instance MonadReader r m => MonadReader r (ReaderT r' m) where
        ask = lift ask
        local m = hoist (local m)

runNoContext :: RaiseT (LoggerT IO) a -> IO a
runNoContext a = do
        (r, log) <- runLoggerT $ runRaiseT a
        mapM_ print log
        case r of
                Left ex -> error (show ex)
                Right res -> return res


runWithRTC' :: RegionTypeContext ->
        RaiseT (ReaderT ProcedureContext (LoggerT IO)) a ->
        IO a
runWithRTC' rtc a = do
        provers <- initProvers
        let pc = ProcedureContext rtc provers []
        (r, log) <- runLoggerT $ runReaderT (runRaiseT a) pc
        mapM_ print log
        case r of
                Left ex -> error (show ex)
                Right res -> return res

runWithRTC :: RegionTypeContext ->
        ChoiceM (RaiseT (ReaderT ProcedureContext (LoggerT IO))) a ->
        IO (Maybe a)
runWithRTC rtc a = do
        provers <- initProvers
        let pc = ProcedureContext rtc provers []
        (r, log) <- runLoggerT $ runReaderT (runRaiseT (firstChoice a)) pc
        mapM_ print log
        case r of
                Left ex -> print ex >> return Nothing
                Right res -> return res

fromEmptySS :: Monad m => StateT (SymbState Assumptions) m a -> m a
fromEmptySS a = evalStateT a emptySymbState

goAdmit :: (Monad m) => StateT (SymbState Assertions) m a -> StateT (SymbState Assumptions) m a
goAdmit = wrapStateT (fmap emptyAssertions) (fmap admitAssertions)

p0 = initialPos "[None]"

impliesWithRTC :: RegionTypeContext -> Assrt -> Assrt -> IO Bool
impliesWithRTC rtc a1 a2 = do
        res <- runWithRTC rtc $ flip runStateT emptySymbState $ do
                        produceAssrt False a1
                        goAdmit $ do
                                consumeAssrt a2
                                justCheck
        case res of
                Just _ -> return True
                Nothing -> return False

implies = impliesWithRTC emptyRTContext

isValid :: Assrt -> IO Bool
isValid a = do
        res <- runWithRTC emptyRTContext $ flip runStateT emptySymbState $ goAdmit $ do
                consumeAssrt a
                justCheck
        case res of
                Just _ -> return True
                Nothing -> return False

isSatisfiable :: Assrt -> IO Bool
isSatisfiable a = do
        res <- runWithRTC emptyRTContext $ flip runStateT emptySymbState $ do
                produceAssrt False a
                isConsistent
        case res of
                Just (Just b, _) -> return b
                _ -> return False

                

{-
test0 = runWithRTC t_RTContext0 $ flip runStateT emptySymbState $ do
        produceAssrt False (AssrtConj p0 (AssrtSpatial p0 (SARegion (Region p0 "Test" "r" [] (VarValExpr p0 (WildCard p0)))))
                (AssrtSpatial p0 (SAGuards (Guards p0 "r" [NamedGuard p0 "B", NamedGuard p0 "C" ]))))
        printSymbState
        goAdmit $ do
            consumeAssrt (AssrtSpatial p0 (SAGuards (Guards p0 "r" [PermGuard p0 "D" (VarPermExpr p0 (Variable p0 "u")), PermGuard p0 "D" (VarPermExpr p0 (Variable p0 "v"))])))
            ask >>= justCheck
        liftIO $ putStrLn "foo"
        printSymbState
--}
