{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
module ProverDatatypes where
import Prelude hiding (sequence,foldl,foldr,elem,mapM_,mapM)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.State hiding (mapM_,mapM)
import Data.Foldable
import Data.Traversable
import Data.Typeable
import Control.Monad hiding (mapM_,mapM)
import Control.Monad.Reader.Class



class Refreshable v where
        freshen :: v -> [v]

instance Refreshable String where
        freshen s = [ s ++ show x | x <- [0..] ]



data Literal a v = LPos (a v) | LNeg (a v) deriving (Functor, Foldable, Traversable)

instance Show (a v) => Show (Literal a v) where
        show (LPos x) = show x
        show (LNeg x) = "¬ " ++ show x

data PermissionExpression v = PEFull
                        | PEZero
                        | PEVar v
                        | PESum (PermissionExpression v) (PermissionExpression v)
                        | PECompl (PermissionExpression v)
                        deriving (Eq,Ord,Functor, Foldable, Traversable)
instance Show v => Show (PermissionExpression v) where
        show PEFull = "1"
        show PEZero = "0"
        show (PESum e1 e2) = "(" ++ show e1 ++ " + " ++ show e2 ++ ")"
        show (PECompl e) = "(1 - " ++ show e ++ ")"
        show (PEVar v) = show v

instance Monad PermissionExpression where
        return = PEVar
        (PEVar v) >>= b = b v
        PESum x y >>= b = PESum (x >>= b) (y >>= b)
        PECompl e >>= b = PECompl (e >>= b)
        PEFull >>= _ = PEFull
        PEZero >>= _ = PEZero

-- Note: could probably get rid of Expression and use Monad instead: return takes place of var
class Expression e where
        var :: v -> e v

instance Expression PermissionExpression where
        var = PEVar

data PermissionAtomic v =
                 PAEq (PermissionExpression v) (PermissionExpression v)
                | PADis (PermissionExpression v) (PermissionExpression v)
                deriving (Functor, Foldable, Traversable, Eq, Ord)

class ExpressionSub c e where
        exprSub :: (v -> e w) -> c v -> c w

instance Monad m => ExpressionSub m m where
        exprSub a b = b >>= a

instance ExpressionSub PermissionExpression e => ExpressionSub PermissionAtomic e where
        exprSub s (PAEq x y) = PAEq (exprSub s x) (exprSub s y)
        exprSub s (PADis x y) = PADis (exprSub s x) (exprSub s y)

instance Show v => Show (PermissionAtomic v) where
        show (PAEq v1 v2) = show v1 ++ " =p= " ++ show v2
        show (PADis v1 v2) = show v1 ++ " # " ++ show v2


type PermissionLiteral = Literal PermissionAtomic

instance (ExpressionSub a e) => ExpressionSub (Literal a) e where
        exprSub s (LPos a) = LPos (exprSub s a)
        exprSub s (LNeg a) = LNeg (exprSub s a)


data ValueExpression v =
          VEConst Integer
        | VEVar v
        | VEPlus (ValueExpression v) (ValueExpression v)
        | VEMinus (ValueExpression v) (ValueExpression v)
        | VETimes (ValueExpression v) (ValueExpression v)
        deriving (Eq,Ord,Functor,Foldable,Traversable)

instance Expression ValueExpression where
        var = VEVar

instance Monad ValueExpression where
        return = VEVar
        (VEConst c) >>= b = VEConst c
        (VEVar v) >>= b = b v
        VEPlus e1 e2 >>= b = VEPlus (e1 >>= b) (e2 >>= b)
        VEMinus e1 e2 >>= b = VEMinus (e1 >>= b) (e2 >>= b)
        VETimes e1 e2 >>= b = VETimes (e1 >>= b) (e2 >>= b)

instance Show a => Show (ValueExpression a) where
        show (VEConst n) = show n
        show (VEVar v) = show v
        show (VEPlus e1 e2) = "(" ++ show e1 ++ " + " ++ show e2 ++  ")"
        show (VEMinus e1 e2) = "(" ++ show e1 ++ " - " ++ show e2 ++  ")"
        show (VETimes e1 e2) = "(" ++ show e1 ++ " * " ++ show e2 ++  ")"

data ValueAtomic v =
          VAEq (ValueExpression v) (ValueExpression v)
        | VALt (ValueExpression v) (ValueExpression v)
        deriving (Eq,Ord,Functor,Foldable,Traversable)

instance ExpressionSub ValueExpression e => ExpressionSub ValueAtomic e where
        exprSub s (VAEq v1 v2) = VAEq (exprSub s v1) (exprSub s v2)
        exprSub s (VALt v1 v2) = VALt (exprSub s v1) (exprSub s v2)


instance Show a => Show (ValueAtomic a) where
        show (VAEq e1 e2) = show e1 ++ " =v= " ++ show e2
        show (VALt e1 e2) = show e1 ++ " < " ++ show e2

class ValueExpressionCastable t v where
        toValueExpr :: t v -> ValueExpression v

instance ValueExpressionCastable ValueExpression v where
        toValueExpr = id


($+$) :: (ValueExpressionCastable a v, ValueExpressionCastable b v) => a v -> b v -> ValueExpression v
($+$) x y = toValueExpr x `VEPlus` toValueExpr y
($-$) :: (ValueExpressionCastable a v, ValueExpressionCastable b v) => a v -> b v -> ValueExpression v
($-$) x y = toValueExpr x `VEMinus` toValueExpr y
($*$) :: (ValueExpressionCastable a v, ValueExpressionCastable b v) => a v -> b v -> ValueExpression v
($*$) x y = toValueExpr x `VETimes` toValueExpr y

infixl 6 $+$, $-$
infixl 6 $*$

{-
instance Num (ValueExpression v) where
        (+) = VEPlus
        (-) = VEMinus
        (*) = VETimes
        fromInteger = VEConst
-}

class StringVariable v where
        -- Convert a variable to a string, for passing to a prover
        -- Each variable should have a unique string representation:
        -- if two variables have the same representation, they are
        -- considered to be the same variable.
        -- Care should be taken to ensure that variables conform to
        -- syntax restrictions: [a-zA-Z0-9_]* 
        varToString :: v -> String

data VariableType = VTPermission | VTValue | VTRegionID
        deriving (Eq, Ord, Typeable)

class Provers a where
        permissionsProver :: a -> FOF PermissionAtomic String -> IO (Maybe Bool)
        valueProver :: a -> FOF ValueAtomic String -> IO (Maybe Bool)

data ProverRecord = Provers {
                _permissionsProver :: FOF PermissionAtomic String -> IO (Maybe Bool),
                _valueProver :: FOF ValueAtomic String -> IO (Maybe Bool)
                }

valueCheck :: (MonadIO m, MonadReader r m, Provers r, StringVariable v) =>
        FOF ValueAtomic v -> m (Maybe Bool)
valueCheck f = do
                p <- ask
                let sf = fmap varToString f
                liftIO $ do
                        putStrLn $ "Checking: " ++ show sf
                        r <- valueProver p sf
                        print r
                        return r


instance Provers ProverRecord where
        permissionsProver = _permissionsProver
        valueProver = _valueProver


instance Show VariableType where
        show VTPermission = "Permission"
        show VTValue = "Value"





data FOF a v =
          FOFForAll v (FOF a v)
        | FOFExists v (FOF a v)
        | FOFAtom (a v)
        | FOFAnd (FOF a v) (FOF a v)
        | FOFOr (FOF a v) (FOF a v)
        | FOFImpl (FOF a v) (FOF a v)
        | FOFNot (FOF a v)
        | FOFFalse
        | FOFTrue
        deriving (Eq, Ord, Functor, Foldable, Traversable)
        
instance (Show (a v), Show v) => Show (FOF a v) where
        show FOFFalse = "_|_"
        show FOFTrue = "T"
        show (FOFAtom a) = show a
        show (FOFNot f) = "¬ " ++ show f
        show (FOFAnd f1 f2) = "(" ++ show f1 ++ " /\\ " ++ show f2 ++ ")"
        show (FOFOr f1 f2) = "(" ++ show f1 ++ " \\/ " ++ show f2 ++ ")"
        show (FOFImpl f1 f2) = "(" ++ show f1 ++ " => " ++ show f2 ++ ")"
        show (FOFForAll v f1) = "![" ++ show v ++ "](" ++ show f1 ++ ")"
        show (FOFExists v f1) = "?[" ++ show v ++ "](" ++ show f1 ++ ")"

class FreeVariables f where
        foldrFree :: (Eq a) => (a -> b -> b) -> b -> f a -> b
        freeIn :: (Eq v) => v -> f v -> Bool
        freeIn v = foldrFree ( (||) . (== v) ) False
        freeVariables :: (Ord v) => f v -> Set.Set v
        freeVariables = foldrFree Set.insert Set.empty

instance (Foldable a) => FreeVariables (FOF a) where
        foldrFree f = ff []
                where
                        ff bound x (FOFForAll v s) = ff (v : bound) x s
                        ff bound x (FOFExists v s) = ff (v : bound) x s
                        ff bound x (FOFAtom a) = foldr (ignoring bound) x a
                        ff bound x (FOFAnd f1 f2) = ff bound (ff bound x f2) f1
                        ff bound x (FOFOr f1 f2) = ff bound (ff bound x f2) f1
                        ff bound x (FOFImpl f1 f2) = ff bound (ff bound x f2) f1
                        ff bound x (FOFNot f') = ff bound x f'
                        ff bound x _ = x
                        ignoring l u v = if u `elem` l then v else f u v

literalToFOF :: Literal a v -> FOF a v
literalToFOF (LPos a) = FOFAtom a
literalToFOF (LNeg a) = FOFNot $ FOFAtom a

class ExpressionCASub c e where
        exprCASub :: (Refreshable v, Eq v) => (v -> e v) -> c v -> c v

instance (ExpressionSub a e, Functor a, Foldable a, Functor e, Monad e) => ExpressionCASub (FOF a) e where
        exprCASub s = unhelpSub . helpSub (fmap Right . s) 
            where
                -- helpSub :: (v -> e (Either v v)) -> FOF a v -> FOF a (Either v v)
                helpSub s (FOFForAll v p) = FOFForAll (Left v) (helpSub (\x -> if x == v then return $ Left v else s x) p)
                helpSub s (FOFExists v p) = FOFExists (Left v) (helpSub (\x -> if x == v then return $ Left v else s x) p)
                helpSub s (FOFAtom a) = FOFAtom (exprSub s a)
                helpSub s (FOFAnd p1 p2) = FOFAnd (helpSub s p1) (helpSub s p2)
                helpSub s (FOFOr p1 p2) = FOFOr (helpSub s p1) (helpSub s p2)
                helpSub s (FOFImpl p1 p2) = FOFImpl (helpSub s p1) (helpSub s p2)
                helpSub s (FOFNot p) = FOFNot (helpSub s p)
                helpSub _ FOFFalse = FOFFalse
                helpSub _ FOFTrue = FOFTrue
                -- unhelpSub :: FOF a (Either v v) -> FOF a v
                unhelpSub f = fmap refresh f
                        where
                                refresh (Left v) = head $ filter (\x -> not $ freeIn (Right x) f) ( v : freshen v )
                                refresh (Right v) = v

($=$) :: (ValueExpressionCastable a v, ValueExpressionCastable b v) => a v -> b v -> FOF ValueAtomic v
($=$) x y = FOFAtom $ toValueExpr x `VAEq` toValueExpr y
($/=$) :: (ValueExpressionCastable a v, ValueExpressionCastable b v) => a v -> b v -> FOF ValueAtomic v
($/=$) x y = FOFNot $ FOFAtom $ toValueExpr x `VAEq` toValueExpr y
($<$) :: (ValueExpressionCastable a v, ValueExpressionCastable b v) => a v -> b v -> FOF ValueAtomic v
($<$) x y = FOFAtom $ toValueExpr x `VALt` toValueExpr y
($<=$) :: (ValueExpressionCastable a v, ValueExpressionCastable b v) => a v -> b v -> FOF ValueAtomic v
($<=$) x y = FOFNot $ FOFAtom $ toValueExpr y `VALt` toValueExpr x

infix 4 $=$, $/=$, $<$, $<=$
