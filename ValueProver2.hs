module ValueProver2 where
import ProverDatatypes
import Z3.Monad

v = evalZ3 getVersion

convValueExpression :: (MonadZ3 z3) => (v -> AST) -> ValueExpression v -> z3 AST
convValueExpression s (VEConst i) = mkInt i
convValueExpression s (VEVar v) = return $ s v
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

convValueAtomic :: (MonadZ3 z3) => (v -> AST) -> ValueAtomic v -> z3 AST
convValueAtomic s (VAEq e1 e2) = do
                c1 <- convValueExpression s e1
                c2 <- convValueExpression s e2
                mkEq c1 c2
convValueAtomic s (VALt e1 e2) = do
                c1 <- convValueExpression s e1
                c2 <- convValueExpression s e2
                mkLt c1 c2

convValueFOF :: (Show v, Eq v, MonadZ3 z3) => Sort -> (v -> AST) -> FOF ValueAtomic v -> z3 AST
convValueFOF intS s (FOFForAll v f) = do
                        si <- mkStringSymbol (show v)
                        sk <- mkConst si intS
                        x <- convValueFOF intS (\w -> if w == v then sk else s w) f
                        mkForall [] [si] [intS] x
convValueFOF intS s (FOFExists v f) = do
                        si <- mkStringSymbol (show v)
                        sk <- mkConst si intS
                        x <- convValueFOF intS (\w -> if w == v then sk else s w) f
                        mkExists [] [si] [intS] x
convValueFOF intS s (FOFAtom a) = convValueAtomic s a
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

valueCheck :: (Eq v, Show v) => FOF ValueAtomic v -> IO (Maybe Bool)
valueCheck f = evalZ3 $ do
                intS <- mkIntSort
                c <- convValueFOF intS (\v -> error $ "Unquantified variable " ++ show v ++ " in formula:\n" ++ show f) f
                c' <- mkNot c
                assertCnstr c'
                r <- check
                return $ case r of
                        Sat -> Just False
                        Unsat -> Just True
                        _ -> Nothing



