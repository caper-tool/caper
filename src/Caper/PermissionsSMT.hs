{-# LANGUAGE ScopedTypeVariables #-}

module Caper.PermissionsSMT where

import Numeric
import Data.List
import Data.Bits
import Data.Maybe

import Caper.ProverDatatypes

toBinary :: Int -> Integer -> String
toBinary bitcount v = "#b" ++ (tail $ showIntAtBase 2 (head . show)
                ((v .&. (2 ^ (2 ^ bitcount) - 1)) + 2 ^ (2 ^ bitcount)) "")

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

smtify :: Eq v => String -> [v] -> FOF PermissionAtomic v -> String
smtify bits ctx (FOFForAll v f) = "(forall ((" ++ newbits ++ " (_ BitVec "
                ++ show (2^(l+1)) ++ "))) (=> (= " ++ bits ++
                " (bvor ((_ extract " ++ show (2^l - 1) ++ " 0) " ++ newbits
                ++ ") ((_ extract " ++ show (2^(l+1) - 1) ++ " " ++ show (2^l)
                ++ ") " ++ newbits ++ "))) " ++ smtify newbits ctx' f ++ "))" 
        where
                ctx' = v : ctx
                l = length ctx
                newbits = "bits" ++ (show (l + 1)) 
smtify bits ctx (FOFExists v f) = "(exists ((" ++ newbits ++ " (_ BitVec "
                ++ show (2^(l+1)) ++ "))) (and (= " ++ bits ++
                " (bvor ((_ extract " ++ show (2^l - 1) ++ " 0) " ++ newbits
                ++ ") ((_ extract " ++ show (2^(l+1) - 1) ++ " " ++ show (2^l)
                ++ ") " ++ newbits ++ "))) " ++ smtify newbits ctx' f ++ "))" 
        where
                ctx' = v : ctx
                l = length ctx
                newbits = "bits" ++ (show (l + 1))
smtify bits ctx (FOFAtom atm) = "(and " ++ intercalate " "
        ["(= " ++ toBin 0 ++
                " (bvand " ++ bits ++ " " ++ toBin msk ++ "))"
                | msk <- masks atm ] ++ ")"
        where
                toBin = toBinary (length ctx)
                masks (PADis e1 e2) = (smtpe ctx e1 .&. smtpe ctx e2) : smtdjs ctx e1 ++ smtdjs ctx e2
                masks (PAEq e1 e2) = (smtpe ctx (PECompl e1) .&. smtpe ctx e2) : 
                        (smtpe ctx e1 .&. smtpe ctx (PECompl e2)) :
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