" Vim syntax file
" Language: Caper
" Maintainer: Thomas Dinsdale-Young
" Latest Revision: 10th July 2013

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

syn region caperAnnotation start=' ' end=';' contained
syn keyword caperAnnotationDeclaration requires ensures nextgroup=caperAnnotation
syn keyword caperAnnotationDeclaration region predicate

syn match caperSquareError '\]'
syn region caperDereference start='\[' end='\]' contains=caperOperator,caperNumber transparent keepend

syn region caperCommment start="//" skip="\\$" end="$" keepend

syn match caperCurlyError "}"
syn region caperFunctionBody start='{' end='}' contains=ALLBUT,caperKeyword,caperCurlyError,caperAnnotation fold

let b:current_syntax = "caper"

hi def link caperOperator       Operator
hi def link caperSquareError    Error
hi def link caperCurlyError     Error
hi def link caperKeyword        Statement
hi def link caperStatement      Statement
hi def link caperCommment       Comment
hi def link caperRepeat         Repeat
hi def link caperNumber         Constant
hi def link caperConstant       Constant
hi def link caperDereference    Operator
hi caperAnnotationDeclaration   gui=bold term=bold guifg=Red
hi def link caperAnnotation     Preproc
