" Vim syntax file
" Language: Chalice
" Author: Kuat Yessenov
" Date: 7/14/2010

syntax clear
syntax case match
syntax keyword chaliceFunction function method predicate
syntax keyword chaliceTypeDef class channel module
syntax keyword chaliceConditional if then else 
syntax keyword chaliceRepeat foreach while
syntax keyword chaliceStatement assert assume call reorder share unshare acquire release lock rd downgrade free fold unfold fork join wait signal send receive 
syntax keyword chaliceKeyword external var ghost returns where const new between and above below waitlevel lockbottom this result holds refines replaces spec by transforms
syntax keyword chaliceType int bool seq token
syntax keyword chaliceLogic invariant requires ensures lockchange
syntax keyword chaliceOperator forall exists old fresh old credit acc unfolding in eval ite rd
syntax keyword chaliceBoolean true false
  
syntax region chaliceString start=/"/ skip=/\\"/ end=/"/

syntax match chaliceComment /\/\/.*/
syntax region chaliceComment start="/\*" end="\*/"

syntax match chaliceNumber /\d\+\>/
syntax match chaliceIdentifier /\<\w\+\>/

syntax match chaliceOperator "==>"
syntax match chaliceOperator "<==>"
syntax match chaliceOperator ":="
syntax match chaliceOperator "<<"

highlight link chaliceFunction Function
highlight link chaliceTypeDef Typedef
highlight link chaliceConditional Conditional
highlight link chaliceRepeat Repeat
highlight link chaliceKeyword Keyword
highlight link chaliceType Type
highlight link chaliceLogic Debug
highlight link chaliceComment Comment
highlight link chaliceString String
highlight link chaliceNumber Number
highlight link chaliceOperator Operator
highlight link chaliceStatement Statement
highlight link chaliceBoolean Boolean 
