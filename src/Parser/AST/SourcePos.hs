{-# LANGUAGE TemplateHaskell #-}
module Parser.AST.SourcePos where

import Text.ParserCombinators.Parsec
import Language.Haskell.TH

class HasSourcePos t where
        sourcePos :: t -> SourcePos

makeSourcePos :: Name -> Q [Dec]
makeSourcePos nm = do
        inf <- reify nm
        case inf of
                TyConI (DataD _ _ _ cs _) -> do
                        spcs <- mapM makeClause cs
                        return [InstanceD [] (AppT (ConT ''HasSourcePos) (ConT nm)) [FunD 'sourcePos spcs]]
                _ -> fail "makeSourcePos: Expected the name of a data type"
        where
                spn = mkName "sp"
                makeClause constr = do
                        pat <- makePattern constr
                        return $ Clause [pat] (NormalB (VarE spn)) []
                makePattern (NormalC n sts) = return $ ConP n 
                        [if x == ConT ''SourcePos then VarP spn else WildP | (_,x) <- sts ]
                makePattern (RecC n sts) = return $ ConP n
                        [if x == ConT ''SourcePos then VarP spn else WildP | (_,_,x) <- sts ]
                makePattern (ForallC _ _ c) = makePattern c
                makePattern _ = fail "makeSourcePos: infix constructors are not supported."
