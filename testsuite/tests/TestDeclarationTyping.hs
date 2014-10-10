
import Caper.DeclarationTyping
import Caper.Parser.AST
import Caper.Parser.Parser

import Infrastructure

s = "region Region1(r,x) {\
\  guards 0;\
\  interpretation {\
\    0 : Region1(r,x,0);\
\    1 : x |-> 0;\
\  }\
\  actions {\
\    : 0 ~> 1;\
\  }\
\}"



main = print $ parseString s
