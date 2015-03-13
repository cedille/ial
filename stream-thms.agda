module stream-thms where

open import eq
open import nat
open import level
open import stream

----------------------------------------------------------------------
-- definition of stream equality
----------------------------------------------------------------------

-- xs =𝕊 ys iff they give equal (≡) answers for all observations
_=𝕊_ : ∀{ℓ}{A : Set ℓ}{n : ℕ} → 𝕊i A n → 𝕊i A n → Set ℓ
_=𝕊_{ℓ}{A}{n} xs ys = ∀ (o : ℕi n) → xs o ≡ ys o

----------------------------------------------------------------------
-- syntax
----------------------------------------------------------------------

infix 4 _=𝕊_ 

----------------------------------------------------------------------
-- theorems
----------------------------------------------------------------------

----------------------------------------------------------
-- if streams are equal, their heads and tail𝕊s are equal
----------------------------------------------------------
=𝕊-head : ∀{ℓ}{A : Set ℓ} {n : ℕ} (xs ys : 𝕊i A n) → xs =𝕊 ys → head𝕊 xs ≡ head𝕊 ys
=𝕊-head xs ys p = p izero

=𝕊-tail𝕊 : ∀{ℓ}{A : Set ℓ}{n : ℕ} {xs ys : 𝕊i A (suc n)} → xs =𝕊 ys → tail𝕊 xs =𝕊 tail𝕊 ys
=𝕊-tail𝕊 p o = p (isuc o)

----------------------------------------------------------
-- stream equality is an equivalence
----------------------------------------------------------
=𝕊-refl : ∀{ℓ}{A : Set ℓ} → {n : ℕ}(xs : 𝕊i A n) → xs =𝕊 xs
=𝕊-refl xs o = refl

=𝕊-sym : ∀{ℓ}{A : Set ℓ}{n : ℕ}{xs ys : 𝕊i A n} → xs =𝕊 ys → ys =𝕊 xs
=𝕊-sym p o = sym (p o)

=𝕊-trans : ∀{ℓ}{A : Set ℓ}{n : ℕ}{xs ys zs : 𝕊i A n} → xs =𝕊 ys → ys =𝕊 zs → xs =𝕊 zs
=𝕊-trans p1 p2 o = trans (p1 o) (p2 o)
