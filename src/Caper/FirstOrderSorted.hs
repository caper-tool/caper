module Caper.FirstOrderSorted where

data VSort v = SrtVar | SrtInt | SrtRegionID | SrtPermission | SrtList VSort
        deriving (Eq, Ord)

-- data SFOF srt rel exp var =
    