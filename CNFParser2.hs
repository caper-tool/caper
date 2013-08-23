import Text.Parsec
import Text.Parsec.Language (emptyDef)
import Text.Parsec.Char
import qualified Text.Parsec.Token as P
import DPLL2
import Data.Bits
import PMaybe

decimal = P.decimal (P.makeTokenParser emptyDef)

parseCnf :: Parsec String st [[(Bool, Integer)]]
parseCnf = do
        skipMany comment
        (varcount, clausecount) <- problem
        res <- many1 (try clause)
        skipMany anyChar
        eof
        return res

comment :: Parsec String st ()
comment = do
        spaces
        char 'c'
        skipMany (noneOf "\r\n")
        oneOf "\r\n"
        return ()

problem :: Parsec String st (Integer, Integer)
problem = do
        spaces
        char 'p'
        spaces
        string "cnf"
        spaces
        vars <- decimal
        spaces
        clauses <- decimal
        spaces
        return (vars, clauses)

literal :: Parsec String st (Bool, Integer)
literal = do
        pos <- option True (char '-' >> return False)
        l <- decimal
        spaces
        return (pos, l)

clauseEnd :: Parsec String st ()
clauseEnd = (char '0' >> (eof <|> skipMany1 space)) <|> eof

clause :: Parsec String st [(Bool, Integer)]
clause = do
        r <- manyTill literal clauseEnd
        return r

toClause :: [(Bool, Integer)] -> Clause
toClause l = tc l 0 0
        where
                tc [] x y = Clause (x, y)
                tc ((pos,tl):lits) p m = let lit' = fromInteger tl - 1 in
                        if m `testBit` lit' then
                                Clause (0,0)
                        else
                                tc lits
                                        (if pos then p `setBit` lit' else p)
                                        (m `setBit` lit')

loadFile :: String -> IO [Clause]
loadFile fn = do
        f <- readFile fn
        let Right res = runParser parseCnf () fn f
        return $ map toClause res

dpllFile :: String -> IO (Maybe Model)
dpllFile fn = do
        cs <- loadFile fn
        m <- doRunPMaybe $ dpll $! cs
        case m of
                Nothing -> return m
                Just mod -> do
                        putStrLn $ if validate mod cs then "Model found" else "Model invalid!" 
                        return m

dpllFiles :: [String] -> IO ()
dpllFiles [] = return ()
dpllFiles (f:fs) = do
        res <- dpllFile f
        print $! res
        dpllFiles fs

main = do
        --dpllFile "cnf/uuf250-077.cnf"
        --dpllFile "cnf/UUF50.218.1000/uuf50-01.cnf"
        dpllFiles ["cnf/UUF100.430.1000/uuf100-0" ++ show n ++ ".cnf" | n <- [1..1000]]
