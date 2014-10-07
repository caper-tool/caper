import Test.HUnit
import Control.Monad
import Text.Parsec (parse)
import Data.Either

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

ppe = parse permissionExpression ""

testNegative = pve "- - 1" `eeq` (Right (UnaryValExpr p0 ValNegation (UnaryValExpr p0 ValNegation (ConstValExpr p0 1))))

stripParens :: String -> String
stripParens = filter (not . (`elem` "()"))

eqWOParens :: (Eq a, Show a, Show b) => (String -> Either b a) -> String -> Test
eqWOParens prse s = (stripParens s) ~: (r0 === r1) ~? ("expected: " ++ show r0 ++ "\nobserved: " ++ show r1)
        where
                r0 = prse s
                r1 = prse (stripParens s)

valAssocTests = "Associativity/precedence tests" ~: map (eqWOParens pve) [
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

checkNoParse :: (String -> Either a b) -> String -> Test
checkNoParse prse s = s ~: either (\_ -> True) (\_ -> False) (prse s) ~? "Should not parse"

valNegationTests = "Negation non-parsing tests" ~: map (checkNoParse pve) [
        "- - 1", "--1", "-- 1", "- -1", "+1", "1+-1","1 + - 1"]

eqWOParensNP :: (Eq a, Show a, Show b) => (String -> Either b a) -> String -> Test
eqWOParensNP prse s = (stripParens s) ~: (r0 `eeq` r1) ~? ("expected: " ++ show r0 ++ "\nobserved: " ++ show r1)
        where
                r0 = prse s
                r1 = prse (stripParens s)

valEQNPTests = "Should either not parse without parens or give same result" ~: map (eqWOParensNP pve) [
        "(1 + (- 1))",
        "(1+(-1))",
        "(a+(-2))",
        "(a+(-b))",
        "(1+(-(-2)))",
        "(3*(-7))",
        "(2/(-2))",
        "(a-(-b))",
        "(1-(-2))",
        "(-(-2))"]

permAssocTests = "Associativity/precedence tests" ~: map (eqWOParens ppe) [
        "(1p $ 0p)",
        "((1p $ 0p) $ 1p)",
        "(((a$b)$c)$d)",
        "(~a)"
        ]
permEQNPTests = "Should either not parse without parens or give same result" ~: map (eqWOParensNP ppe) [
        "(a$(~b))",
        "((~a)$b)",
        "(~(~1p))"]

