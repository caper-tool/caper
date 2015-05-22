module Caper.Provers.Values.Z3 where
import Caper.ProverDatatypes
import Z3.Monad
import Control.Exception hiding (assert)

--v = evalZ3 getVersion

convValueExpression :: (MonadZ3 z3) => (v -> z3 AST) -> ValueExpression v -> z3 AST
convValueExpression s (VEConst i) = mkInteger i
convValueExpression s (VEVar v) = s v
convValueExpression s (VEPlus e1 e2) = do
                c1 <- convValueExpression s e1
                c2 <- convValueExpression s e2
                mkAdd [c1, c2]
convValueExpression s (VEMinus e1 e2) = do
                c1 <- convValueExpression s e1
                c2 <- convValueExpression s e2
                mkSub [c1, c2]
convValueExpression s (VETimes e1 e2) = do
                c1 <- convValueExpression s e1
                c2 <- convValueExpression s e2
                mkMul [c1, c2]

convValueAtomic :: (MonadZ3 z3) => (v -> z3 AST) -> ValueAtomic v -> z3 AST
convValueAtomic s (VAEq e1 e2) = do
                c1 <- convValueExpression s e1
                c2 <- convValueExpression s e2
                mkEq c1 c2
convValueAtomic s (VALt e1 e2) = do
                c1 <- convValueExpression s e1
                c2 <- convValueExpression s e2
                mkLt c1 c2

convValueFOF :: (Show v, Eq v, MonadZ3 z3) => Sort -> (v -> Int) -> FOF ValueAtomic v -> z3 AST
convValueFOF intS s (FOFForAll v f) = do
                        si <- mkStringSymbol (show v)
                        x <- convValueFOF intS (\w -> if w == v then 0 else 1 + s w) f
                        mkForall [] [si] [intS] x
convValueFOF intS s (FOFExists v f) = do
                        si <- mkStringSymbol (show v)
                        x <- convValueFOF intS (\w -> if w == v then 0 else 1 + s w) f
                        mkExists [] [si] [intS] x
convValueFOF intS s (FOFAtom a) = convValueAtomic (\v -> mkBound (s v) intS) a
convValueFOF intS s (FOFAnd f1 f2) = do
                c1 <- convValueFOF intS s f1
                c2 <- convValueFOF intS s f2
                mkAnd [c1, c2]
convValueFOF intS s (FOFOr f1 f2) = do
                c1 <- convValueFOF intS s f1
                c2 <- convValueFOF intS s f2
                mkOr [c1, c2]
convValueFOF intS s (FOFImpl f1 f2) = do
                c1 <- convValueFOF intS s f1
                c2 <- convValueFOF intS s f2
                mkImplies c1 c2
convValueFOF intS s (FOFNot f1) = do
                c1 <- convValueFOF intS s f1
                mkNot c1
convValueFOF intS s FOFFalse = mkFalse
convValueFOF intS s FOFTrue = mkTrue

valueCheck :: (Eq v, Show v) => Maybe Int -> FOF ValueAtomic v -> IO (Maybe Bool)
valueCheck timeout f = evalZ3With Nothing opts $ do
                intS <- mkIntSort
                c <- convValueFOF intS (\v -> error $ "Unquantified variable " ++ show v ++ " in formula:\n" ++ show f) f
                c' <- mkNot c
                k <- astToString c'
                assert c'
                r <- check
                x <- withModel showModel
                {-case x of
                        (_, Just x') -> error $ k ++ "\n" ++ x'
                        _ -> return ()-}
                return $ case r of
                        Sat -> Just False
                        Unsat -> Just True
                        _ -> Nothing
        where
                opts = case timeout of
                        (Just x) -> if x > 0 then opt "timeout" x else stdOpts
                        _ -> stdOpts

valueProverInfo :: IO String
valueProverInfo = (do
        ver <- evalZ3 getVersion
        return $ "Z3 library, version " ++ show ver) `catch`
        (\e -> return $ "Failed to invoke Z3:\n" ++ show (e :: SomeException))
