import DPLL2

import Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec.Language (emptyDef)


lexer = P.makeTokenParser emptyDef

decimal = P.decimal lexer

cnfFile :: GenParser Char st (Integer,[[(Bool,Integer)]])
cnfFile = do
        many comment
        (vars, clauses) <- cnfProblem
        cs <- many (try clause)
        skipMany anyChar
        return (vars, cs)

comment :: GenParser Char st ()
comment = spaces >> char 'c' >> skipMany (noneOf "\r\n") >> oneOf "\r\n" >> return ()

minus :: GenParser Char st Bool
minus = option True $ do
        char '-'
        return False

cnfProblem = do
        spaces
        char 'p'
        spaces
        string "cnf"
        spaces
        vars <- decimal
        spaces
        clauses <- decimal
        return (vars,clauses)

mval = do
        pos <- minus
        val <- decimal
        return (pos,val)
clauseEnd :: GenParser Char st ()
clauseEnd = (char '0' >> return ()) <|> eof

clause :: GenParser Char st [(Bool,Integer)]
clause = spaces >> manyTill (do
                v <- mval
                spaces
                return v) clauseEnd
        
main = do
        Right (_, input) <- parseFromFile cnfFile "cnftest/uf20-01.cnf"
        print $ dpll $ map toClause input
