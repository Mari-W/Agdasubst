% open import Data.String using (String)
%
% data Const : Set where
%   fork : Const
%   recv send term : Const
%
expr : Type

✶            : expr
#_           : "Const" -> expr
‵_           : "String" -> expr
λx_          : (expr -> expr) -> expr
⟨_,_⟩        : expr -> expr -> expr
_·_          : expr -> expr -> expr
let✶_ın_     : expr -> expr -> expr
let⟨x,y⟩_ın_ : expr -> (expr -> expr -> expr) -> expr
