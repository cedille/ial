module vector-sort where

open import level
open import bool
open import nat
open import product
open import vector

insert𝕍 : ∀{ℓ}{A : Set ℓ}{n : ℕ} → (_<_ : A → A → 𝔹) → (_≅_ : A → A → 𝔹) → A → 𝕍 A n → Σi ℕ (λ m → 𝕍 A (suc m))
insert𝕍 _<_ _≅_ x []𝕍 = , [ x ]𝕍
insert𝕍 _<_ _≅_ x (y ::𝕍 ys) with x < y
... | tt = , x ::𝕍 y ::𝕍 ys
... | ff with x ≅ y 
... | tt = , y ::𝕍 ys
... | ff with (insert𝕍 _<_ _≅_ x ys)
... | , r = , y ::𝕍 r

insertion-sort𝕍 : ∀{ℓ}{A : Set ℓ}{n : ℕ} → (_<_ : A → A → 𝔹) → (_≅_ : A → A → 𝔹) → 𝕍 A (suc n) → Σi ℕ (λ m → 𝕍 A (suc m))
insertion-sort𝕍 _ _ (x ::𝕍 []𝕍) = , [ x ]𝕍
insertion-sort𝕍 _<_ _≅_ (x ::𝕍 (y ::𝕍 ys)) with insertion-sort𝕍 _<_ _≅_ (y ::𝕍 ys)
... | , (z ::𝕍 zs) = insert𝕍 _<_ _≅_ x (z ::𝕍 zs)

test-insertion-sort𝕍 = insertion-sort𝕍 _<_ _=ℕ_ (3 ::𝕍 5 ::𝕍 2 ::𝕍 7 ::𝕍 1 ::𝕍 2 ::𝕍 3 ::𝕍 9 ::𝕍 []𝕍)
