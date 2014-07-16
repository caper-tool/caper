{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}
{- |The Exceptions module provides for execution-time failure reporting.
   The exceptions defined here are /not/ for programmer errors (e.g. assertion
   failures) or generally recoverable exceptions.  The system provides a
   mechanism for annotating exceptions with contextual information (for
   identifying the cause of the exception).
 -}
module Exceptions(
        module Exceptions)
        where
import Data.Typeable
import Control.Monad.Exception
import Control.Monad.Trans.Either
import Control.Monad.Trans
import Text.ParserCombinators.Parsec

import Utils.MonadHoist
import TypingContext
import ProverDatatypes

-- |Abbreviation for 'TypeUnificationException VariableID VariableType'.
type TUException = TypeUnificationException VariableID VariableType

-- |The data type 'CaperException' represents exceptions that may be
-- raised as a result of an execution-time failure that the user should
-- be able to correct.
data CaperException =
        -- |'SyntaxNotImplemented' indicates that a piece of syntax
        -- (which is supported by the parser) is not yet implemented
        -- in the tool.  The parameter should describe the syntax.
        SyntaxNotImplemented String
        -- |'TypesNotUnifiable' indicates that the inferred type of a
        -- variable does not match the expected type.
        | TypesNotUnifiable TUException
        deriving (Eq, Typeable)

instance Show CaperException where
        show (SyntaxNotImplemented s) = "The following syntax is not yet implemented: " ++ s
        show (TypesNotUnifiable tue) = show tue

-- |The data type 'ExceptionContext' represents contextual information
-- about the cause of a 'CaperException'.
data ExceptionContext =
        StringContext String
        | SourcePosContext SourcePos

instance Show ExceptionContext where
        show (StringContext s) = s
        show (SourcePosContext sp) = show sp

-- |The 'MonadRaise' class supports raising 'CaperException's and
-- adding contextual information
class MonadRaise m where
        raise :: CaperException -> m a
        addContext :: ExceptionContext -> m a -> m a

addSPContext :: (MonadRaise m) => SourcePos -> m a -> m a
addSPContext = addContext . SourcePosContext

-- |The 'RaiseT' monad transformer provides an instance for 'MonadRaise'.
-- It is simply defined in terms of 'EitherT'.
type RaiseT = EitherT ([ExceptionContext], CaperException)

instance (Monad m, Functor m) => MonadRaise (RaiseT m) where
        raise ex = left ([], ex)
        addContext ctx = bimapEitherT (\(ctxx, ex) -> (ctx : ctxx, ex)) id

instance (MonadTrans t, MonadHoist t, Monad m, MonadRaise m) => MonadRaise (t m) where
        raise = lift . raise
        addContext ctx = hoist $ addContext ctx

-- |Propagate a 'TUException' as a 'CaperException'.
liftTUFailure :: (Monad m, MonadRaise m) => Either TUException a -> m a
liftTUFailure (Left e) = raise (TypesNotUnifiable e)
liftTUFailure (Right r) = return r
