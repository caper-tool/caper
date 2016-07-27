{-# LANGUAGE TemplateHaskell #-}
module Caper.Parser.AST.SourcePos where

import Text.ParserCombinators.Parsec
import Language.Haskell.TH

class HasSourcePos t where
        sourcePos :: t -> SourcePos

makeSourcePos :: Name -> Q [Dec]
makeSourcePos nm = do
        inf <- reify nm
        case inf of
                TyConI (DataD _ _ _ _ cs _) -> do
                        spcs <- mapM makeClause cs
                        return [InstanceD Nothing [] (AppT (ConT ''HasSourcePos) (ConT nm)) [FunD 'sourcePos spcs]]
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


makeSPEq :: Name -> Q [Dec]
makeSPEq nm = do
        inf <- reify nm
        case inf of
                TyConI (DataD _ _ _ _ cs _) -> do
                        spcs <- mapM makeClause cs
                        let spcs' = spcs ++ [Clause [WildP, WildP] (NormalB (ConE 'False)) []]
                        return [InstanceD Nothing [] (AppT (ConT ''Eq) (ConT nm)) [FunD '(==) spcs']]
                _ -> fail "makeSPEq: Expected the name of a data type"
        where
                makeClause (NormalC n sts) = do
                        let patterns = [ConP n [VarP $ mkName $ '_' : x : show i |
                                                 i <- [1..length sts]]
                                             | x <- "ab"]
                        let conjs = [InfixE (Just $ VarE $ mkName $ "_a" ++ show i) (VarE '(==)) (Just $ VarE $ mkName $ "_b" ++ show i)
                                | ((_,t), i) <- zip sts [(1::Int)..],
                                        t /= ConT ''SourcePos]
                        return $ Clause patterns (NormalB $ AppE (VarE 'and) (ListE conjs)) []
                makeClause _ = fail "makeSPEq: Only normal constructors are supported"
