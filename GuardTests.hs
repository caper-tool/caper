import Prelude hiding (catch,mapM,sequence,foldl,mapM_)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.Exception
import Control.Monad hiding (mapM)
import Control.Monad.State hiding (mapM_,mapM)
import Control.Monad.Trans.Maybe
import ProverDatatypes
import PermissionsInterface
import Guards
import PermissionsE
import Permissions
import Prover
import Provers
import Control.Monad.List hiding (mapM)
import Choice

gt1 = ProductGT (NamedPermissionGT "A") (SumGT (NamedPermissionGT "B") (ProductGT (NamedGT "C") (NamedGT "D")))

gt2 = ProductGT (SumGT (NamedPermissionGT "A") (NamedPermissionGT "Z")) (SumGT (NamedPermissionGT "B") (ProductGT (NamedGT "C") (NamedGT "D")))

{--
cont1 = snd $ runState x emptyContext
        where
                x = do
                        foo <- checkBindVariable () "foo" VTPermission
                        assertPermissionFalse $ PAEq (PEVar foo) (PEFull)
                        assertPermissionFalse $ PAEq (PEVar foo) (PEZero)
                        bar <- checkBindVariable () "bar" VTPermission
                        assertPermissionFalse $ PAEq (PEVar bar) (PEFull)
                        assertPermissionFalse $ PAEq (PEVar bar) (PEZero)

cont2 = execState x cont1
        where
                x = do
                        assertPermissionFalse $ PADis (PEVar $ VIDNamed () "foo") (PEVar $ VIDNamed () "bar")
--}

gd1 = GD (Map.fromList [("A", NoGP), ("B", NoGP)])
gd2 = GD (Map.fromList [("B", NoGP)])
gd3 = GD (Map.fromList [("A", PermissionGP PEFull), ("B", PermissionGP (PEVar "foo"))])
gd4 = GD (Map.fromList [("A", PermissionGP $ PEVar "bar")])
gd5 = GD (Map.fromList [("A", PermissionGP $ PEVar "zop")])
gd6 = GD (Map.fromList [("A", PermissionGP $ PEVar "zop"), ("B", PermissionGP $ PEVar "zop")])
gd7 = GD (Map.fromList [("A", PermissionGP $ PEVar "bar"), ("B", PermissionGP (PEVar "foo"))])
gd8 = GD (Map.fromList [("A", PermissionGP $ PEVar "foo"), ("D", NoGP), ("C", NoGP)])

vx = VIDNamed "x"
vy = VIDNamed "y"
vfoo = VIDNamed "foo"
vbar = VIDNamed "bar"
vzop = VIDNamed "zop"

asm1 :: Monad m => ProverT m ()
asm1 = do
        declareVars [vx, vy]
        assumeTrue $ VAEq (var vx) (VETimes (VEConst 2) (var vy))

asm2 :: Monad m => ProverT m ()
asm2 = do
        asm1
        assumeFalse $ PAEq (var vfoo) (PEZero)
        assumeFalse $ PAEq (var vfoo) (PEFull)

asm3 :: Monad m => ProverT m ()
asm3 = do
        asm1
        assumeTrue $ PAEq (var vzop) (PEFull)

ast1 :: Monad m => CheckerT m ()
ast1 = assertTrue $ VAEq (VEMinus (var vx) (var vy)) (var vy)
ast2 :: Monad m => CheckerT m ()
ast2 = assertFalse $ VAEq (VEMinus (var vx) (var vy)) (var vy)

doEntTest :: (MonadIO m, MonadPlus m) => Provers -> GuardTypeAST -> Guard String -> ProverT m () -> Guard String -> CheckerT m () -> m (Guard VariableID)
doEntTest ps guardType assumeGuard assumptions assertGuard assertions = runProverT $ do
        g1 <- declareAssumptionNames assumeGuard
        assumptions
        check (do
                g2 <- declareAssertionNames assertGuard
                assertions
                guardEntailment guardType g1 g2)
                ps

entTest :: Provers -> GuardTypeAST -> Guard String -> ProverT (ListT IO) () -> Guard String -> CheckerT (ListT IO) () -> IO [(Guard VariableID)]
entTest ps guardType assumeGuard assumptions assertGuard assertions = runListT $ doEntTest ps guardType assumeGuard assumptions assertGuard assertions

entTestM ps gt ag as tg ts = runMaybeT $ doEntTest ps gt ag as tg ts

getProvers = getInternalZ3Provers

et gt asmg asm astg ast = do
        ps <- getProvers
        entTest ps gt asmg asm astg ast
etm gt asmg asm astg ast = do
        ps <- getProvers
        entTestM ps gt asmg asm astg ast

etc gt asmg asm astg ast = do
        ps <- getProvers
        firstChoice $ doEntTest ps gt asmg asm astg ast

main :: IO ()
main = do
        ps <- getEZ3Provers
        r <- entTest ps gt1 gd1 asm1 gd1 ast1
        print r

{--
gtest :: (PermissionsProver p) => p -> Context -> Guard VariableID -> Guard EVariable -> IO (Maybe (Guard EVariable, Context))
gtest prover c g1 g2 = runMaybeT $ runStateT x c
        where
                x :: StateT Context (MaybeT IO) (Guard EVariable)
                x = do
                        r <- guardPrimitiveEntailment prover g1 g2 
                        return $ fst r

main :: IO ()
main = do
        epp <- makeEPProver
        r <- gtest epp cont2 gd7 gd6a
        putStrLn $ show r
--}
