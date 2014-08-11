module Caper.Utils.LiteralFileQQ where
import Language.Haskell.TH
import Language.Haskell.TH.Quote

literalFile :: QuasiQuoter
literalFile = quoteFile QuasiQuoter {
                quoteExp = return . LitE . StringL,
                quotePat = undefined,
                quoteType = undefined,
                quoteDec = undefined
        }
