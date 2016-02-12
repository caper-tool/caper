" Vim syntax file
" Language: Caper
" Maintainer: Thomas Dinsdale-Young
" Latest Revision: 21st October 2015

if exists("b:current_syntax")
  finish
endif

" Keywords
syn keyword caperKeyword function
syn keyword caperStatement contained var if else alloc CAS return break continue skip
syn keyword caperRepeat contained do while
syn keyword caperConstant true false

syn match caperOperator ":="
syn match caperOperator "="
syn match caperOperator "+"
syn keyword caperOperator and or not

syn match caperNumber '\d\+' contained display



syn keyword caperRegAn guards 
syn keyword caperRegAn interpretation 
syn keyword caperRegAn actions

syn region caperAnnotation start='\s' end=';' contained
syn keyword caperAnnotationDeclaration requires ensures invariant assert nextgroup=caperAnnotation
syn keyword caperToplevelDeclaration region
syn keyword caperToplevelDeclaration predicate

syn match caperSquareError '\]'
syn region caperDereference start='\[' end='\]' contains=caperOperator,caperNumber,caperComment transparent keepend

syn region caperComment start="//" skip="\\$" end="$" keepend
syn region caperComment start="/\*" end="\*/" keepend

syn match caperCurlyError "}"
syn region caperFunctionBody start='{' end='}' contains=ALLBUT,caperKeyword,caperCurlyError,caperAnnotation fold

let b:current_syntax = "caper"

hi def link caperOperator       Operator
hi def link caperSquareError    Error
hi def link caperCurlyError     Error
hi def link caperKeyword        Statement
hi def link caperStatement      Statement
hi def link caperComment        Comment
hi def link caperRepeat         Repeat
hi def link caperNumber         Constant
hi def link caperConstant       Constant
hi def link caperDereference    Operator
hi caperAnnotationDeclaration   gui=bold term=bold guifg=Red
hi caperRegAn                   gui=bold term=bold guifg=Red
hi def link caperToplevelDeclaration Statement
hi def link caperAnnotation     Preproc

