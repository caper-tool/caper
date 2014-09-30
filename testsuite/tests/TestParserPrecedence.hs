import Test.HUnit
import Control.Monad
import Text.Parsec (parse)

import Caper.Parser.AST
import Caper.Parser.Parser

import Infrastructure

eeq :: (Eq y) => Either x y -> Either x y -> Bool
eeq (Right a) (Right b) = a == b
eeq _ _ = True

(===) :: (Eq y) => Either x y -> Either x y -> Bool
(===) (Right a) (Right b) = a == b
(===) _ _ = False

pve = parse valueExpressionParser ""

testNegative = pve "- - 1" `eeq` (Right (UnaryValExpr p0 ValNegation (UnaryValExpr p0 ValNegation (ConstValExpr p0 1))))

stripParens :: String -> String
stripParens = filter (not . (`elem` "()"))

eqWOParens :: String -> Test
eqWOParens s = (stripParens s) ~: (r0 === r1) ~? ("expected: " ++ show r0 ++ "\nobserved: " ++ show r1)
        where
                r0 = pve s
                r1 = pve (stripParens s)

assocTests = "Associativity/precedence tests" ~: map eqWOParens [
        "(1 + 2) + 3",
        "(1 - 2) - 3",
        "(a * b) * c",
        "(a / b) / c",
        "(1 + 2) - 3",
        "(1 - 2) + 3",
        "(((1 + 2) - 3) + 4)",
        "(((1 -2) + 3) - 4)",
        "1 + (2 * 3)",
        "(1 * 2) + 3",
        "(a * b) + (3 * 4)",
        "(1 + (a * b)) + c",
        "1 - (2 * 3)",
        "(1 * 2) - 3",
        "1 + (2 / 3)",
        "(1 / 2) + 3",
        "1 - (2 / 3)",
        "(1 / 2) - 3",
        "(1 * 2) / 3",
        "(1 / 2) * 3",
        "((1 * 2) / 3) * 4",
        "1 - ((2 * 3) / 4)",
        "2 - ((1 / 3) * 4)"
        ]
