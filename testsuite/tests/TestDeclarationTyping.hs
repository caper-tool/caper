import Text.Parsec (parse)

import Caper.DeclarationTyping
import Caper.Parser.AST
import Caper.Parser.Parser

import Infrastructure

s = "region RegionA(r,x) {\
\  guards 0;\
\  interpretation {\
\    0 : RegionA(r,x,0);\
\    1 : x |-> 0;\
\  }\
\  actions {\
\    : 0 ~> 1;\
\  }\
\}"



main = print $ parseString s
