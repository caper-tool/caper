module Caper.FirstOrderSorted where

data Sort v = SrtVar v | SrtInt | SrtRegionID | SrtPermission | SrtList VSort
        deriving (Eq, Ord)


data IntExp se = IEConst Integer | IEPlus se se | IEMinus se se | IETimes se se
data ListExp se = LstENil | LstECons se se

data LogicalExp var = LEVar var | IntExp 

data SFOF srt rel exp var =
    SFOFAtom (rel exp var)
    