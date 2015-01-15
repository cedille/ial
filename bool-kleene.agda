-- Kleene's three-valued logic 

module bool-kleene where

data 𝔹ₖ : Set where
  tt : 𝔹ₖ
  ff : 𝔹ₖ
  uu : 𝔹ₖ

infix  7 ~ₖ_
infixr 6 _&&ₖ_
infixr 5 _||ₖ_ 
--infixr 4 _impₖ_ 

~ₖ_ : 𝔹ₖ → 𝔹ₖ
~ₖ tt = ff
~ₖ ff = tt
~ₖ uu = uu

-- and
_&&ₖ_ : 𝔹ₖ → 𝔹ₖ → 𝔹ₖ
tt &&ₖ b = b
ff &&ₖ b = ff
uu &&ₖ ff = ff
uu &&ₖ b = b

-- or
_||ₖ_ : 𝔹ₖ → 𝔹ₖ → 𝔹ₖ
tt ||ₖ b = tt
ff ||ₖ b = b
uu ||ₖ tt = tt
uu ||ₖ b = uu

-- implication
_impₖ_ : 𝔹ₖ → 𝔹ₖ → 𝔹ₖ 
tt impₖ b2 = b2
ff impₖ b2 = tt
uu impₖ tt = tt
uu impₖ b = uu
