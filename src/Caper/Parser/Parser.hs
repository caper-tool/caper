{-# OPTIONS_GHC -fno-warn-unused-do-bind -fno-warn-missing-signatures #-}
module Caper.Parser.Parser(
        parseFile,
        parseString,
        parseAExpression,
        parseBExpression,
        aExpressionParser,
        statementParser,
        parseStatement,
        parseValueExpression,
        valueExpressionParser,
        permissionExpression,
        regionAssertion
        ) where

import Control.Monad (liftM)
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token
import Caper.Parser.AST
import Control.Applicative ((*>))


languageDef =
  emptyDef { Token.commentStart    = "/*"
           , Token.commentEnd      = "*/"
           , Token.commentLine     = "//"
           , Token.identStart      = letter
           , Token.identLetter     = alphaNum <|> char '_'  -- FIXED? : '_' should be allowed (non-initially) in identifiers
           , Token.caseSensitive   = True
           , Token.reservedNames   = [ "if"
                                     , "else"
                                     , "while"
                                     , "do"
                                     , "skip"
                                     , "true"
                                     , "false"
                                     , "not"
                                     , "and"
                                     , "or"
                                     , "return"
                                     , "function"
                                     , "fork"
                                     , "requires"
                                     , "ensures"
                                     , "invariant"
                                     , "assert"
                                     , "region"
                                     , "guards"
                                     , "interpretation"
                                     , "actions"
                                     , "predicate"
                                     , "("
                                     , ")"
                                     , "{"
                                     , "}"
                                     , "]"
                                     , "["
                                     , "0p"
                                     , "1p"
                                     , "#cells"
                                     , "_"
                                     ]
           , Token.reservedOpNames = ["+", "-", "*", "/", ":="
                                     , "=", "!=", "<", ">", ">=", "<="
                                     , "and", "or", "not", "?", ":"
                                     , "&*&", "=p=", "=v=", "$", "!"
                                     , "==", "|->", "@", "~>", "|", "%"
                                     ]
           }

lexer = Token.makeTokenParser languageDef

identifier = Token.identifier lexer -- parses an identifier
reserved   = Token.reserved   lexer -- parses a reserved name
reservedOp = Token.reservedOp lexer -- parses an operator
parens     = Token.parens     lexer -- parses surrounding parenthesis
braces     = Token.braces     lexer -- parses surrounding braces
brackets   = Token.brackets   lexer -- parses surrounding brackets
natural    = Token.natural    lexer -- parses a natural number
semi       = Token.semi       lexer -- parses a semicolon
comma      = Token.comma      lexer -- parses a comma
whiteSpace = Token.whiteSpace lexer -- parses whitespace
symbol     = Token.symbol     lexer

rIdentifier :: Parser String
rIdentifier =
  do s <- upper
     r <- identifier
     return $ s : r

pIdentifier :: Parser String
pIdentifier =
  do s <- lower
     r <- identifier
     return $ s : r

parser :: Parser [Declr]
parser = do
    whiteSpace
    decs <- sequenceOfDeclr
    eof
    return decs

sequenceOfDeclr :: Parser [Declr]
sequenceOfDeclr = sepBy declaration whiteSpace

declaration :: Parser Declr
declaration =  liftM DeclrFun function
           <|> liftM DeclrReg region

function :: Parser FunctionDeclr
function =
  do pos  <- getPosition
     reserved "function"
     var  <- identifier
     args <- parens $ sepBy identifier comma
     req  <- optionMaybe $ (do { reserved "requires"; a <- assertion; semi; return a})
     ens  <- optionMaybe $ (do { reserved "ensures"; a <- assertion; semi; return a})
     stmt <- braces sequenceOfStmt
     return $ FunctionDeclr pos var req ens args stmt

region :: Parser RegionDeclr
region =
  do pos <- getPosition
     reserved "region"
     var <- rIdentifier
     args <- parens $ sepBy identifier comma
     reserved "{"
     reserved "guards"
     gds <- topLevelGuardDeclaration
     semi
     reserved "interpretation"
     itr <- braces $ endBy interpretation semi
     reserved "actions"
     act <- braces $ endBy action semi
     reserved "}"
     return $ RegionDeclr pos var args gds itr act

topLevelGuardDeclaration :: Parser TopLevelGuardDeclr
topLevelGuardDeclaration =  (do { char '0'; return ZeroGuardDeclr})
                        <|> (do { gds <- guardDeclaration; return $ SomeGuardDeclr gds})

guardDeclaration :: Parser GuardDeclr
guardDeclaration = buildExpressionParser guardDeclarationOperators guardDeclarationTerm

guardDeclarationOperators = [ [Infix  (do { pos <- getPosition; reservedOp "*"; return (ProductGD pos)}) AssocLeft]
                          , [Infix  (do { pos <- getPosition; reservedOp "+"; return (SumGD pos    )}) AssocLeft]
                          ]

guardDeclarationTerm =  parens guardDeclaration
                    <|> permissionGuardDeclaration
                    <|> namedGuardDeclaration
                    <|> parametrisedGuardDeclaration

permissionGuardDeclaration =
  do pos <- getPosition
     reservedOp "%"
     n   <- identifier
     return $ PermissionGD pos n

namedGuardDeclaration =
  do pos <- getPosition
     n   <- identifier
     return $ NamedGD pos n

parametrisedGuardDeclaration =
  do pos <- getPosition
     reservedOp "#"
     n   <- identifier
     return $ ParametrisedGD pos n

interpretation :: Parser StateInterpretation
interpretation =
  do pos <- getPosition
     c   <- conditions
     s   <- valueExpression
     reservedOp ":"
     i <- assertion
     return $ StateInterpretation pos c s i

conditions :: Parser [PureAssrt]
conditions =  try (do { d <- sepBy pureAssertion comma; reservedOp "|"; return d })
          <|> return []

action :: Parser Action
action =
  do pos  <- getPosition
     c    <- conditions
     g    <- sepBy guard (reservedOp "*")
     reservedOp ":"
     pre  <- valueExpression
     reservedOp "~>"
     post <- valueExpression
     return $ Action pos c g pre post

sequenceOfStmt :: Parser Stmt
sequenceOfStmt =
  do pos  <- getPosition
     list <- (sepEndBy statement whiteSpace)
     return $ SeqStmt pos list

statement :: Parser Stmt
statement =  ifElseStatement
         <|> whileStatement
         <|> doWhileStatement
         <|> forkStatement
         <|> assignStatement
         <|> otherAssignStatement
         <|> returnStatement
         <|> skipStatement
         <|> assertStatement

ifElseStatement :: Parser Stmt
ifElseStatement =
  do pos  <- getPosition
     reserved "if"
     cond  <- parens bExpression
     stmt1 <- braces sequenceOfStmt
     e     <- optionMaybe $ reserved "else"
     case e of
       Nothing -> return $ IfElseStmt pos cond stmt1 (SkipStmt pos)
       Just _l -> do
                    stmt2 <- braces sequenceOfStmt
                    return $ IfElseStmt pos cond stmt1 stmt2

whileStatement :: Parser Stmt
whileStatement =
  do pos  <- getPosition
     reserved "while"
     cond <- parens bExpression
     inv <- optionMaybe $ reserved "invariant" *> assertion
     stmt <- braces sequenceOfStmt
     return $ WhileStmt pos inv cond stmt

doWhileStatement :: Parser Stmt
doWhileStatement =
  do pos  <- getPosition
     reserved "do"
     inv <- optionMaybe $ reserved "invariant" *> assertion
     stmt <- braces sequenceOfStmt
     reserved "while"
     cond <- parens bExpression
     semi
     return $ DoWhileStmt pos inv stmt cond

forkStatement :: Parser Stmt
forkStatement =
  do pos  <- getPosition
     reserved "fork"
     fun  <- identifier
     args <- parens $ sepBy aExpression comma
     semi
     return $ ForkStmt pos fun args

assignStatement :: Parser Stmt
assignStatement =
  do pos   <- getPosition
     expr1 <- brackets aExpression
     reservedOp ":="
     expr2 <- aExpression
     semi
     return $ AssignStmt pos expr1 expr2

otherAssignStatement :: Parser Stmt
otherAssignStatement =
  do pos <- getPosition
     var <- identifier
     args <- optionMaybe $ parens $ sepBy aExpression comma
     case args of
       Nothing -> reservedOp ":=" >> (derefStatement pos var
                                      <|> callStatement pos var
                                      <|> localAssignStatement pos var)
       Just l  -> semi >> return (CallStmt pos Nothing var l)

derefStatement :: SourcePos -> String -> Parser Stmt
derefStatement pos var =
  do expr <- brackets aExpression
     semi
     return $ DerefStmt pos var expr

callStatement :: SourcePos -> String -> Parser Stmt
callStatement pos var =
  do expr <- aExpression
     case expr of
       VarAExpr _ n -> do args <- optionMaybe $ parens $ sepBy aExpression comma
                          semi
                          case args of
                            Nothing -> return $ LocalAssignStmt pos var $ VarAExpr pos n
                            Just l  -> return $ CallStmt pos (Just var) n l
       _otherwise   -> semi >> return (LocalAssignStmt pos var expr)

localAssignStatement :: SourcePos -> String -> Parser Stmt
localAssignStatement pos var =
  do expr <- aExpression
     semi
     return $ LocalAssignStmt pos var expr

returnStatement :: Parser Stmt
returnStatement =
  do pos <- getPosition
     reserved "return"
     expr <- optionMaybe aExpression
     semi
     return $ ReturnStmt pos expr

skipStatement :: Parser Stmt
skipStatement =
  do pos <- getPosition
     reserved "skip"
     semi
     return $ SkipStmt pos

assertStatement :: Parser Stmt
assertStatement =
  do pos <- getPosition
     reserved "assert"
     assrt <- assertion
     semi
     return $ AssertStmt pos assrt

aExpression :: Parser AExpr
aExpression = buildExpressionParser aOperators aTerm

bExpression :: Parser BExpr
bExpression = buildExpressionParser bOperators bTerm

aOperators = [ [Prefix (do { pos <- getPosition; reservedOp "-"; return (NegAExpr pos            )})          ]
             , [Infix  (do { pos <- getPosition; reservedOp "*"; return (BinaryAExpr pos Multiply)}) AssocLeft, Infix  (do { pos <- getPosition; reservedOp "/"; return (BinaryAExpr pos Divide  )}) AssocLeft]
             , [Infix  (do { pos <- getPosition; reservedOp "+"; return (BinaryAExpr pos Add     )}) AssocLeft, Infix  (do { pos <- getPosition; reservedOp "-"; return (BinaryAExpr pos Subtract)}) AssocLeft]
             ]

bOperators = [ [Prefix (do { pos <- getPosition; reservedOp "not"; return (NotBExpr pos            )})          ]
             , [Infix  (do { pos <- getPosition; reservedOp "and"; return (BinaryBExpr pos And     )}) AssocLeft]
             , [Infix  (do { pos <- getPosition; reservedOp "or" ; return (BinaryBExpr pos Or      )}) AssocLeft]
             ]

aTerm =  parens aExpression
     <|> variable
     <|> intConst

variable =
  do pos <- getPosition
     var  <- identifier
     return $ VarAExpr pos var

intConst =
  do pos <- getPosition
     i   <- natural
     return $ ConstAExpr pos i

bTerm =  parens bExpression
     <|> (do { pos <- getPosition; reserved "true"; return (ConstBExpr pos True)})
     <|> (do { pos <- getPosition; reserved "false"; return (ConstBExpr pos False)})
     <|> rExpression

rExpression =
  do pos <- getPosition
     a1  <- aExpression
     op  <- relation
     a2  <- aExpression
     return $ RBinaryBExpr pos op a1 a2

relation =  (reservedOp "=" >> return Equal)
        <|> (reservedOp "!=" >> return NotEqual)
        <|> (reservedOp ">" >> return Greater)
        <|> (reservedOp "<" >> return Less)
        <|> (reservedOp ">=" >> return GreaterOrEqual)
        <|> (reservedOp "<=" >> return LessOrEqual)

assertion :: Parser Assrt
assertion =
  do pos <- getPosition
     a   <- assertion2
     return $ refineAssertion $ a

assertion2 :: Parser Assrt
assertion2 = try (iteAssertion)
         <|> assertionAux

iteAssertion :: Parser Assrt
iteAssertion =
  do pos <- getPosition
     ac  <- pureAssertion
     reservedOp "?"
     a1  <- assertionAux
     reservedOp ":"
     a2  <- assertionAux
     return $ AssrtITE pos ac a1 a2

assertionAux :: Parser Assrt
assertionAux = buildExpressionParser assertionOperators assertionTerm

assertionOperators = [ [Infix  (do { pos <- getPosition; reservedOp "&*&"; return (AssrtConj pos)}) AssocLeft]
                     ]

assertionTerm =  try (parens assertion2)
             <|> try (do { pos <- getPosition; a <- spatialAssertion; return (AssrtSpatial pos a)})
             <|> (do { pos <- getPosition; a <- pureAssertion; return (AssrtPure pos a)})

pureAssertion :: Parser PureAssrt
pureAssertion = buildExpressionParser pureOperators pureTerm

pureOperators = [ [Prefix (do { pos <- getPosition; reservedOp "!"; return (NotBAssrt pos            )})          ]
             ]

pureTerm =  try (parens pureAssertion)
        <|> (do { pos <- getPosition; reserved "true"; return (ConstBAssrt pos True)})
        <|> (do { pos <- getPosition; reserved "false"; return (ConstBAssrt pos False)})
        <|> try (do { a <- binaryValueAssertion; notFollowedBy (symbol "p" <|> symbol "$"); return a })
        <|> binaryPermissionAssertion
        <|> binaryValueAssertion

binaryVariableAssertion =
  do pos <- getPosition
     e1  <- variableExpression
     br  <- equalityRelation
     e2  <- variableExpression
     return $ BinaryVarAssrt pos br e1 e2

equalityRelation =  (reservedOp "=" >> return EqualRel)
                <|> (reservedOp "!=" >> return NotEqualRel)

binaryValueAssertion =
  do pos <- getPosition
     e1  <- valueExpression
     br  <- valueRelation
     e2  <- valueExpression
     return $ BinaryValAssrt pos br e1 e2

valueRelation =  (do { vo <- equalityRelation; return (ValEquality vo) })
             <|> (reservedOp ">" >> return ValGreater)
             <|> (reservedOp ">=" >> return ValGreaterOrEqual)
             <|> (reservedOp "<" >> return ValLess)
             <|> (reservedOp "<=" >> return ValLessOrEqual)

valueExpression :: Parser ValExpr
valueExpression = buildExpressionParser valueOperators valueTerm

valueOperators = [ [Prefix (do { pos <- getPosition; reservedOp "-"; return (UnaryValExpr pos ValNegation )})]
                 , [Infix  (do { pos <- getPosition; reservedOp "*"; return (BinaryValExpr pos ValMultiply)}) AssocLeft, Infix  (do { pos <- getPosition; reservedOp "/"; return (BinaryValExpr pos ValDivide  )}) AssocLeft]
                 , [Infix  (do { pos <- getPosition; reservedOp "+"; return (BinaryValExpr pos ValAdd     )}) AssocLeft, Infix  (do { pos <- getPosition; reservedOp "-"; return (BinaryValExpr pos ValSubtract)}) AssocLeft]
                 ]

valueTerm =  parens valueExpression
         <|> variableValue
         <|> constValue
         <|> setValue

variableValue =
  do pos <- getPosition
     ve  <- variableExpression
     return $ VarValExpr pos ve

variableExpression :: Parser VarExpr
variableExpression =
  do pos  <- getPosition
     wild <- optionMaybe $ reserved "_"
     case wild of
       Nothing -> do s <- identifier;
                     return $ Variable pos s
       Just _  -> return $ WildCard pos

constValue =
  do pos <- getPosition
     c   <- natural
     return $ ConstValExpr pos c

setValue =
  do pos <- getPosition
     ves <- braces (sepBy valueExpression comma)
     return $ SetValExpr pos ves

binaryPermissionAssertion =
  do pos <- getPosition
     e1  <- permissionExpression
     br  <- permissionRelation
     e2  <- permissionExpression
     return $ BinaryPermAssrt pos br e1 e2

permissionRelation =  (do { pe <- equalityRelation; return (PermEquality pe) })
                  <|> (reservedOp "#" >> return Compatible)

permissionExpression :: Parser PermExpr
permissionExpression = buildExpressionParser permissionOperators permissionTerm

permissionOperators = [ [Prefix (do { pos <- getPosition; reservedOp "~"; return (UnaryPermExpr pos Complement )})]
                      , [Infix  (do { pos <- getPosition; reservedOp "$"; return (BinaryPermExpr pos Composition)}) AssocLeft]
                      ]

permissionTerm =  parens permissionExpression
              <|> (do { pos <- getPosition; reserved "1p"; return (ConstPermExpr pos FullPerm)})
              <|> (do { pos <- getPosition; reserved "0p"; return (ConstPermExpr pos EmptyPerm)})
              <|> variablePermission

variablePermission =
  do pos <- getPosition
     ve  <- variableExpression
     return $ VarPermExpr pos ve

spatialAssertion :: Parser SpatialAssrt
spatialAssertion =  (try (parens spatialAssertionAux) <|> spatialAssertionAux)

spatialAssertionAux :: Parser SpatialAssrt
spatialAssertionAux =  try regionAssertion
                   <|> try cellAssertion
                   <|> try predicate
                   <|> guards

regionAssertion :: Parser SpatialAssrt
regionAssertion =
  do pos  <- getPosition
     t    <- rIdentifier
     symbol "("
     v    <- identifier
     comma
     (args, s) <- remargs <?> "','-separated list of value/permission expressions"
     return $ SARegion (Region pos t v args s)
  where
     remargs = (do
                arg <- (try $ do
                        arg <- anyExpression
                        comma
                        return arg)
                (args',s) <- remargs
                return (arg : args', s))
        <|> (do
                s <- valueExpression
                symbol ")"
                return ([],s))


predicate :: Parser SpatialAssrt
predicate =
  do pos  <- getPosition
     p    <- pIdentifier
     args <- parens (sepBy anyExpression comma)
     return $ SAPredicate (Predicate pos p args)

cellAssertion :: Parser SpatialAssrt
cellAssertion =
  do pos <- getPosition
     e1  <- valueExpression
     reservedOp "|->"
     block <- optionMaybe $ reserved "#cells"
     case block of
       Nothing -> do e2 <- valueExpression
                     return $ SACell (Cell pos e1 e2)
       Just _  -> do e2 <- parens valueExpression
                     return $ SACell (CellBlock pos e1 e2)

guards :: Parser SpatialAssrt
guards =
  do pos   <- getPosition
     ident <- identifier
     reservedOp "@"
     gds   <- guardAux
     return $ SAGuards $ Guards pos ident gds

guardAux :: Parser [Guard]
guardAux =  parens (sepBy guard (reservedOp "*"))
        <|> (do { g <- guard; return [g] })

guard :: Parser Guard
guard =
  do pos <- getPosition
     n   <- identifier
     pe <- optionMaybe $ brackets permissionExpression
     case pe of
       Nothing -> do paras <- optionMaybe $ parens (sepBy anyExpression comma)
                     case paras of
                       Nothing -> do param <- optionMaybe $ braces (do { s <- sepBy anyExpression2 comma; reservedOp "|"; c <- sepBy pureAssertion comma; return (s, c) })
                                     case param of
                                       Nothing -> return $ NamedGuard pos n
                                       Just (s, c)  -> return $ ParamSetGuard pos n s c
                       Just m  -> return $ ParamGuard pos n m
       Just l  -> return $ PermGuard pos n l

-- |Parse an 'AnyExpr', provided it's followed by ',', ';' or ')'.
anyExpression :: Parser AnyExpr
anyExpression =  try (do { e <- variableExpression; checkNext; return (AnyVar e) })
             <|> try (do { e <- permissionExpression; checkNext; return (AnyPerm e) })
             <|> (do { e <- valueExpression; checkNext; return (AnyVal e) })
        where
                checkNext = lookAhead (try (comma <|> semi <|> symbol ")"))

-- |Parse an 'AnyExpr', provided it's followed by ',' or '|'.
anyExpression2 :: Parser AnyExpr
anyExpression2 =  try (do { e <- variableExpression; checkNext; return (AnyVar e) })
              <|> try (do { e <- permissionExpression; checkNext; return (AnyPerm e) })
              <|> (do { e <- valueExpression; checkNext; return (AnyVal e) })
        where
                checkNext = lookAhead (try (comma <|> symbol "|"))


refineAssertion (AssrtPure pos pa)      = AssrtPure pos (refinePureAssertion pa)
refineAssertion a@(AssrtSpatial pos sa) = a
refineAssertion (AssrtConj pos a1 a2)   = AssrtConj pos (refineAssertion a1) (refineAssertion a2)
refineAssertion (AssrtITE pos pa a1 a2) = AssrtITE pos (refinePureAssertion pa) (refineAssertion a1) (refineAssertion a2)

refinePureAssertion (NotBAssrt pos pe) = NotBAssrt pos (refinePureAssertion pe)
refinePureAssertion (BinaryPermAssrt pos (PermEquality br) (VarPermExpr _ e1) (VarPermExpr _ e2)) = (BinaryVarAssrt pos br e1 e2)
refinePureAssertion (BinaryValAssrt pos (ValEquality br) (VarValExpr _ e1) (VarValExpr _ e2)) = (BinaryVarAssrt pos br e1 e2)
refinePureAssertion a = a
--refinePureAssertion a@(BinaryVarAssrt pos br e1 e2) = a
--refinePureAssertion a@(BinaryValAssrt pos br e1 e2) = a

refine refineVariableExpression a@(Variable pos s) = a
refine refineVariableExpression a@(WildCard pos) = a

spatialAssertionParser :: Parser SpatialAssrt
spatialAssertionParser = whiteSpace >> spatialAssertion

parseSpatialAssertion :: String -> SpatialAssrt
parseSpatialAssertion str =
  case parse spatialAssertionParser "" str of
    Left e  -> error $ show e
    Right r -> r

valueExpressionParser :: Parser ValExpr
valueExpressionParser = whiteSpace >> valueExpression

parseValueExpression :: String -> ValExpr
parseValueExpression str =
  case parse valueExpressionParser "" str of
    Left e  -> error $ show e
    Right r -> r

pureAssertionParser :: Parser PureAssrt
pureAssertionParser = whiteSpace >> pureAssertion

parsePureAssertion :: String -> PureAssrt
parsePureAssertion str =
  case parse pureAssertionParser "" str of
    Left e  -> error $ show e
    Right r -> r

assertionParser :: Parser Assrt
assertionParser = whiteSpace >> assertion

parseAssertion :: String -> Assrt
parseAssertion str =
  case parse assertionParser "" str of
    Left e  -> error $ show e
    Right r -> r

functionParser :: Parser FunctionDeclr
functionParser = whiteSpace >> function

parseFunction :: String -> FunctionDeclr
parseFunction str =
  case parse functionParser "" str of
    Left e  -> error $ show e
    Right r -> r

parseString :: String -> [Declr]
parseString str =
  case parse parser "" str of
    Left e  -> error $ show e
    Right r -> r

parseFile :: String -> IO [Declr]
parseFile file =
  do program  <- readFile file
     case parse parser "" program of
       Left e  -> print e >> fail "parse error"
       Right r -> return r

aExpressionParser :: Parser AExpr
aExpressionParser = whiteSpace >> aExpression

parseAExpression :: String -> AExpr
parseAExpression str =
  case parse aExpressionParser "" str of
    Left e  -> error $ show e
    Right r -> r

bExpressionParser :: Parser BExpr
bExpressionParser = whiteSpace >> bExpression

parseBExpression :: String -> BExpr
parseBExpression str =
  case parse bExpressionParser "" str of
    Left e  -> error $ show e
    Right r -> r

statementParser :: Parser Stmt
statementParser = whiteSpace >> sequenceOfStmt

parseStatement :: String -> Stmt
parseStatement str =
  case parse statementParser "" str of
    Left e  -> error $ show e
    Right r -> r
