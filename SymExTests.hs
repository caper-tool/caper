import ProverDatatypes
import Provers
import SymbolicState
import Choice
import Control.Monad.RWS
import AST
import Text.Parsec.Pos
import Parser

posCons = newPos "[console]" 0 0

type MyMonad = MSState ProverRecord (ChoiceM IO)

runMyMv :: [String] -> MyMonad a -> IO (Maybe a)
runMyMv vs m = do
        provers <- initProvers
        firstChoice $ do
                (a, s, w) <- runRWST m provers (emptySymbStateWithVars vs)
                liftIO $ putStrLn "\nFinal state\n===========" >> print s
                return a
runMyM = runMyMv []

runMyMvAll :: [String] -> MyMonad a -> IO [a]
runMyMvAll vs m = do
        provers <- initProvers
        allChoices $ do
                (a, s, w) <- runRWST m provers (emptySymbStateWithVars vs)
                liftIO $ putStrLn "\nFinal state\n===========" >> print s
                return a


test1 :: MyMonad ()
test1 = symExAllocate "x" (parseAExpression "2")

test2 :: MyMonad ()
test2 = test1 >> symExRead "y" (parseAExpression "x + 1")

test3 :: MyMonad ()
test3 = test2 >> symExWrite (parseAExpression "x") (parseAExpression "y + 2")

test4 :: MyMonad ()
test4 = test2 >> symExLocalAssign "z" (parseAExpression "4") >> symExWrite (parseAExpression "x") (parseAExpression "y + z")

test5 :: MyMonad ()
test5 = test4 >> symExRead "y" (parseAExpression "x")

test6 :: MyMonad ()
test6 = do
        test2
        s <- get
        liftIO $ putStrLn "\nPenultimate state\n================"
        liftIO $ print s
        symExRead "y" (parseAExpression "x + 2")

test6a :: MyMonad ()
test6a = do
        symExAllocate "x" (parseAExpression "2")
        symExRead "y" (parseAExpression "x + 2")

test7 :: MyMonad ()
test7 = symExRead "y" (parseAExpression "x")
