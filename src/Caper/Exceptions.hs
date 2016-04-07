{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses,
        OverlappingInstances, UndecidableInstances #-}
{- |The Exceptions module provides for execution-time failure reporting.
   The exceptions defined here are /not/ for programmer errors (e.g. assertion
   failures) or generally recoverable exceptions.  The system provides a
   mechanism for annotating exceptions with contextual information (for
   identifying the cause of the exception).
 -}
module Caper.Exceptions(
        module Caper.ExceptionContext,
        module Caper.Exceptions)
        where
import Data.Typeable
-- import Control.Arrow (first)
import Control.Monad.Trans.Either
import Control.Monad.Trans
import Control.Monad.Reader
import Control.Lens
import Text.ParserCombinators.Parsec
import Data.List

import Caper.ExceptionContext
import Caper.Utils.MonadHoist
import Caper.TypingContext
import Caper.ProverDatatypes

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
        -- |'UndeclaredRegionType' indicates that a region type name
        -- is being used, but has not been declared.  The first field
        -- records the undeclared name.  The second field records a
        -- list of (similar) alternatives.
        | UndeclaredRegionType String [String]
        -- |'TypeMismatch' indicates that an expression of the
        -- expected type (first field) was required, but an expression
        -- of the actual type (second field) was given.
        | TypeMismatch VariableType VariableType
        -- |'ArgumentCountMismatch' indicates that the wrong number
        -- of arguments were supplied (e.g. for a region).  The fields
        -- record @required@ and @actual@, or @-1@ and @actual - required@.
        | ArgumentCountMismatch Int Int
        -- |'IncompatibleGuardOccurrences' indicates that multiple guard
        -- occurences with the same name are incompatible.  This may be
        -- because they are of different types (named/permission) or
        -- there is more than one named guard. 
        | IncompatibleGuardOccurrences String
        -- |'GuardInconsistentWithGuardType' indicates that a guard (labelling
        -- a transition) is not consistent with the guard type for the region.
        | GuardInconsistentWithGuardType String String
        -- |'GuardTypeMultipleOccurrences' indicates that a guard type declares
        -- the same guard more than once.
        | GuardTypeMultipleOccurrences String (Maybe String)
        -- |'OverlappingStateInterpretation' indicates that there is some state
        -- whose interpretation is (potentially) ambiguous.
        | OverlappingStateInterpretation
        -- |'MissingStateInterpretation' indicates that no state interpretations
        -- are provided for a region.  (This could become a parse error.)
        | MissingStateInterpretation
        -- |'OverloadedProcedure' indicates that two procedures with the same
        -- name have been declared.
        | OverloadedProcedure String
        -- |'VerificationFailed' indicates that a given procedure could not be verified.
        | VerificationFailed String
        -- |'UndeclaredFunctionCall' indicates a call to a function that has no declaration.
        | UndeclaredFunctionCall String
        -- |'UnstableStateInterpretation' indicates that a state
        -- interpretation could not be proved to be stable.
        | UnstableStateInterpretation
        deriving (Eq, Typeable)

instance Show CaperException where
        show (SyntaxNotImplemented s) = "The following syntax is not yet implemented: " ++ s
        show (TypesNotUnifiable tue) = show tue
        show (UndeclaredRegionType rt l) = "The region type '" ++ rt ++ "' has not been declared." ++ shw l
                where
                        shw [] = ""
                        shw ll = "\n\tPerhaps you meant: " ++ intercalate ", " ll ++ "."
        show (TypeMismatch expected actual) = "A " ++ show expected ++ " expression was required, but a " ++ show actual ++ " expression was provided."
        show (ArgumentCountMismatch (-1) diff)
                | diff < 0 = show (-diff) ++ " too few arguments were supplied."
                | otherwise = show diff ++ " too many arguments were supplied."
        show (ArgumentCountMismatch required actual) =
                show required ++ " arguments were expected, but " ++ show actual ++ " arguments were supplied."
        show (IncompatibleGuardOccurrences gname) =
                "There were incompatible occurrences of guards named '" ++ gname ++ "'."
        show (GuardInconsistentWithGuardType gd gt) =
                "The guard '" ++ gd ++ "' is not consistent with the guard type '" ++ gt ++ "'."
        show (GuardTypeMultipleOccurrences s Nothing) = "Multiple guards named '" ++ s ++ "' are declared in a guard type."
        show (GuardTypeMultipleOccurrences s (Just gt)) = "Multiple guards named '" ++ s ++ "' are declared in the guard type '" ++ gt ++ "'."
        show OverlappingStateInterpretation =
                "There are multiple possible interpretations for a single region state."
        show MissingStateInterpretation =
                "There are no state interpretations for the region."
        show (OverloadedProcedure pname) = 
                "There are multiple procedures named '" ++ pname ++ "'."
        show (VerificationFailed f) =
                "Failed to verify: " ++ f
        show (UndeclaredFunctionCall f) =
                "Call to undeclared function: " ++ f
        show UnstableStateInterpretation =
                "Could not show state interpretation to be stable."


-- |The 'MonadRaise' class supports raising 'CaperException's and
-- adding contextual information
class MonadRaise m where
        raise :: CaperException -> m a
        addContext :: ExceptionContext -> m a -> m a

addSPContext :: (MonadRaise m) => SourcePos -> m a -> m a
addSPContext = addContext . SourcePosContext

-- |The 'RaiseT' monad transformer provides an instance for 'MonadRaise'.
-- It is simply defined in terms of 'EitherT'.
{-
type RaiseT = EitherT ([ExceptionContext], CaperException)

instance (Monad m, Functor m) => MonadRaise (RaiseT m) where
        raise ex = left ([], ex)
        addContext ctx = bimapEitherT (first ((:) ctx)) id
-}
{-
type RaiseT m = ReaderT [ExceptionContext]
        (EitherT ([ExceptionContext], CaperException) m)
--}

type RaiseT = EitherT ([ExceptionContext], CaperException)
runRaiseT :: Monad m => RaiseT m a -> m (Either ([ExceptionContext], CaperException) a)
runRaiseT = runEitherT
        
instance (Monad m, MonadReader r m, ECLenses r) =>
        MonadRaise (EitherT ([ExceptionContext], CaperException) m) where
        raise ex = do
                ctx <- view exceptionContext
                left (ctx, ex)
        addContext ctx = local (exceptionContext %~ (ctx :))

{-
runRaiseT :: Monad m => RaiseT m a -> m (Either ([ExceptionContext], CaperException) a)
runRaiseT a = runEitherT (runReaderT a [])
--}

instance (MonadTrans t, MonadHoist t, Monad m, MonadRaise m) => MonadRaise (t m) where
        raise = lift . raise
        addContext ctx = hoist $ addContext ctx

-- |Propagate a 'TUException' as a 'CaperException'.
liftTUFailure :: (Monad m, MonadRaise m) => Either TUException a -> m a
liftTUFailure (Left e) = raise (TypesNotUnifiable e)
liftTUFailure (Right r) = return r

liftTUMismatch :: (Monad m, MonadRaise m) =>
        Either (TypeUnificationException a VariableType) b -> m b
liftTUMismatch (Left (TypeUnificationException _ t1 t2)) =
        raise (TypeMismatch t1 t2)
liftTUMismatch (Left (TypeUnificationException2 _ t1 _ t2)) =
        raise (TypeMismatch t1 t2)
liftTUMismatch (Right r) = return r

contextualise :: (Contextual a, MonadRaise m) => a -> m b -> m b
contextualise = addContext . toContext 

showException :: ([ExceptionContext], CaperException) -> String
showException (ec, e) = show e ++ "\n" ++
        concat ["  " ++ show c ++ "\n" | c <- ec]  