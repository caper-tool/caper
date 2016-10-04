{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}

module Caper.Provers.Permissions.SMT (permCheckZ3,permCheckZ3Info) where

import Numeric
import Data.List
import Data.Bits
import Data.Maybe
import Z3.Monad
import Control.Monad
import Control.Exception hiding (assert)
-- import Control.Monad.IO.Class

import Caper.ProverDatatypes

permCheckZ3Info :: IO String
permCheckZ3Info = (do
        ver <- evalZ3 getVersion
        return $ "Z3 library, version " ++ show ver) `catch`
        (\e -> return $ "Failed to invoke Z3:\n" ++ show (e :: SomeException))


toZ3BV :: Int -> Integer -> Z3 AST
toZ3BV bitcount v = 
                mkInt2bv (2^bitcount) =<< mkInteger v

-- | Compute bit mask for a permission expression
smtpe :: forall v. Eq v => [v] -> PermissionExpression v -> Integer
smtpe ctx = pebits
        where
                l = length ctx
                pebits :: PermissionExpression v -> Integer
                pebits PEFull = 2 ^ ((2::Integer) ^ l) - 1
                pebits PEZero = 0
                pebits (PECompl e) = (2 ^ ((2::Integer) ^ l) - 1) `xor` pebits e
                pebits (PESum e1 e2) = pebits e1 .|. pebits e2
                pebits (PEVar v) = msk (fromJust (elemIndex v ctx)) (l - 1)
                msk x ln 
                        | x == 0 = 2 ^ ((2::Integer) ^ ln) - 1
                        | x > 0 = msk (x - 1) (ln - 1) * (2 ^ ((2::Integer) ^ ln) + 1)
                        | otherwise = undefined

-- | Compute bit masks for disjointness implied by a permission expression
smtdjs :: Eq v => [v] -> PermissionExpression v -> [Integer]
smtdjs ctx (PESum e1 e2) = (smtpe ctx e1 .&. smtpe ctx e2) : smtdjs ctx e1 ++ smtdjs ctx e2
smtdjs ctx (PECompl e) = smtdjs ctx e
smtdjs ctx _ = []

z3ifyQuant :: Eq v => Bool -> [v] -> v -> FOF PermissionAtomic v -> Z3 AST
z3ifyQuant isForall ctx v f = do
                -- Old bit vector
                bits <- if l == 0 then toZ3BV 0 1
                        else (mkBound 1 =<< mkBvSort (2^l))
                bsymb <- mkStringSymbol ("bits" ++ show l)
                newbvsort <- mkBvSort (2^(l+1))
                newbits <- mkBound 0 newbvsort
                ex1 <- mkExtract (2^l - 1) 0 newbits
                ex2 <- mkExtract (2^(l+1) - 1) (2^l) newbits
                extracts <- mkBvor ex1 ex2
                cond <- mkEq bits extracts
                rec <- z3ify ctx' f
                if isForall then do
                        imp <- mkImplies cond rec
                        mkForall [] [bsymb] [newbvsort] imp
                    else do
                        cnj <- mkAnd [cond,rec]
                        mkExists [] [bsymb] [newbvsort] cnj
        where
                ctx' = v : ctx
                l = length ctx

z3ify :: Eq v => [v] -> FOF PermissionAtomic v -> Z3 AST
z3ify ctx (FOFForAll v f) = z3ifyQuant True ctx v f
z3ify ctx (FOFExists v f) = z3ifyQuant False ctx v f
z3ify ctx (FOFAtom atm) = do
                bits <- if l == 0 then toBin 1
                        else mkBound 0 =<< mkBvSort (2^l)
                conjs <- forM (masks atm) $ \msk -> do
                        bvand <- mkBvand bits =<< toBin msk
                        zro <- toBin 0
                        mkEq zro bvand
                mkAnd conjs
        where
                l = length ctx
                toBin = toZ3BV l
                masks (PADis e1 e2) = (smtpe ctx e1 .&. smtpe ctx e2) : smtdjs ctx e1 ++ smtdjs ctx e2
                masks (PAEq e1 e2) = (smtpe ctx (PECompl e1) .&. smtpe ctx e2) : 
                        (smtpe ctx e1 .&. smtpe ctx (PECompl e2)) :
                                smtdjs ctx e1 ++ smtdjs ctx e2
                masks (PALte e1 e2) = (smtpe ctx e1 .&. smtpe ctx (PECompl e2)) :
                                smtdjs ctx e1 ++ smtdjs ctx e2
z3ify ctx (FOFAnd f1 f2) = do
                r1 <- z3ify ctx f1
                r2 <- z3ify ctx f2
                mkAnd [r1, r2] 
z3ify ctx (FOFOr f1 f2) = do
                r1 <- z3ify ctx f1
                r2 <- z3ify ctx f2
                mkOr [r1, r2]
z3ify ctx (FOFImpl f1 f2) = do
                r1 <- z3ify ctx f1
                r2 <- z3ify ctx f2
                mkImplies r1 r2
z3ify ctx (FOFNot f1) = mkNot =<< z3ify ctx f1
z3ify ctx FOFFalse = mkFalse
z3ify ctx FOFTrue = mkTrue

permCheckZ3 :: Eq v => Maybe Int -> FOF PermissionAtomic v -> IO (Maybe Bool)
permCheckZ3 timeout f = evalZ3With Nothing stdOpts $ do
                params <- mkParams
                tmo <- mkStringSymbol "timeout"
                paramsSetUInt params tmo (case timeout of
                    Just x -> if x > 0 then toEnum x else 0
                    Nothing -> 0)
                solverSetParams params
                f' <- z3ify [] f
                --liftIO . putStrLn =<< astToString f'
                assert =<< mkNot f'
                r <- check
                return $ case r of
                        Sat -> Just False
                        Unsat -> Just True
                        _ -> Nothing
{-        where
                opts = case timeout of
                        (Just x) -> if x > 0 then opt "TIMEOUT" x else stdOpts
                        _ -> stdOpts
-}

-- The following functions construct string-based queries for an SMT solver.
-- Since this module uses the library interface to Z3, this is not used, but I'm leaving it here in case it
-- is ever useful.

toBinary :: Int -> Integer -> String
toBinary bitcount v = "#b" ++ (tail $ showIntAtBase 2 (head . show)
                ((v .&. (2 ^ ((2::Integer) ^ bitcount) - 1)) + 2 ^ ((2::Integer) ^ bitcount)) "")


smtify :: Eq v => String -> [v] -> FOF PermissionAtomic v -> String
smtify bits ctx (FOFForAll v f) = "(forall ((" ++ newbits ++ " (_ BitVec "
                ++ show (two^(l+1)) ++ "))) (=> (= " ++ bits ++
                " (bvor ((_ extract " ++ show (two^l - 1) ++ " 0) " ++ newbits
                ++ ") ((_ extract " ++ show (two^(l+1) - 1) ++ " " ++ show (two^l)
                ++ ") " ++ newbits ++ "))) " ++ smtify newbits ctx' f ++ "))" 
        where
                two = 2 :: Int
                ctx' = v : ctx
                l = length ctx
                newbits = "bits" ++ (show (l + 1)) 
smtify bits ctx (FOFExists v f) = "(exists ((" ++ newbits ++ " (_ BitVec "
                ++ show (two^(l+1)) ++ "))) (and (= " ++ bits ++
                " (bvor ((_ extract " ++ show (two^l - 1) ++ " 0) " ++ newbits
                ++ ") ((_ extract " ++ show (two^(l+1) - 1) ++ " " ++ show (two^l)
                ++ ") " ++ newbits ++ "))) " ++ smtify newbits ctx' f ++ "))" 
        where
                two = 2 :: Int
                ctx' = v : ctx
                l = length ctx
                newbits = "bits" ++ (show (l + 1))
smtify bits ctx (FOFAtom atm) = "(and " ++ unwords
        ["(= " ++ toBin 0 ++
                " (bvand " ++ bits ++ " " ++ toBin msk ++ "))"
                | msk <- masks atm ] ++ ")"
        where
                toBin = toBinary (length ctx)
                masks (PADis e1 e2) = (smtpe ctx e1 .&. smtpe ctx e2) : smtdjs ctx e1 ++ smtdjs ctx e2
                masks (PAEq e1 e2) = (smtpe ctx (PECompl e1) .&. smtpe ctx e2) : 
                        (smtpe ctx e1 .&. smtpe ctx (PECompl e2)) :
                                smtdjs ctx e1 ++ smtdjs ctx e2
                masks (PALte e1 e2) = (smtpe ctx e1 .&. smtpe ctx (PECompl e2)) :
                                smtdjs ctx e1 ++ smtdjs ctx e2
smtify bits ctx (FOFAnd f1 f2) = "(and " ++ smtify bits ctx f1 ++ " " ++
                                smtify bits ctx f2 ++ ")"
smtify bits ctx (FOFOr f1 f2) = "(or " ++ smtify bits ctx f1 ++ " " ++
                                smtify bits ctx f2 ++ ")"
smtify bits ctx (FOFImpl f1 f2) = "(=> " ++ smtify bits ctx f1 ++ " " ++
                                smtify bits ctx f2 ++ ")"
smtify bits ctx (FOFNot f1) = "(not " ++ smtify bits ctx f1 ++ ")"
smtify bits ctx FOFFalse = "false"
smtify bits ctx FOFTrue = "true"

pfofToSMT :: Eq v => FOF PermissionAtomic v -> String
pfofToSMT = smtify "#b1" []
