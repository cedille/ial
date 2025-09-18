module bool-thms where

open import bool
open import eq
open import sum
open import product
open import product-thms

~~-elim : ∀ (b : 𝔹) → ~ ~ b ≡ b
~~-elim tt = refl
~~-elim ff = refl

&&-idem : ∀ {b} → b && b ≡ b
&&-idem{tt} = refl
&&-idem{ff} = refl

||-idem : ∀{b} → b || b ≡ b
||-idem{tt} = refl
||-idem{ff} = refl

||≡ff₁ : ∀ {b1 b2} → b1 || b2 ≡ ff → b1 ≡ ff
||≡ff₁ {ff} p = refl

||≡ff₂ : ∀ {b1 b2} → b1 || b2 ≡ ff → b2 ≡ ff
||≡ff₂ {ff}{ff} p = refl

||≡ff : ∀ {b1 b2} → b1 || b2 ≡ ff → b1 ≡ ff ∧ b2 ≡ ff
||≡ff {ff} {ff} eq = refl , refl

||-tt : ∀ (b : 𝔹) → b || tt ≡ tt
||-tt tt = refl
||-tt ff = refl

||-ff : ∀ (b : 𝔹) → b || ff ≡ b
||-ff tt = refl
||-ff ff = refl

||-cong₁ : ∀ {b1 b1' b2} → b1 ≡ b1' → b1 || b2 ≡ b1' || b2
||-cong₁ refl = refl

||-cong₂ : ∀ {b1 b2 b2'} → b2 ≡ b2' → b1 || b2 ≡ b1 || b2'
||-cong₂ p rewrite p = refl

ite-same : ∀{ℓ}{A : Set ℓ} → 
           ∀(b : 𝔹) (x : A) → 
           (if b then x else x) ≡ x
ite-same tt x = refl
ite-same ff x = refl

ite-arg : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'} → (f : A → B)(b : 𝔹)(x y : A) → (f (if b then x else y)) ≡ (if b then f x else f y)
ite-arg f tt x y = refl
ite-arg f ff x y = refl

𝔹-contra : ff ≡ tt → ∀{ℓ} {P : Set ℓ} → P
𝔹-contra ()

||-split : ∀ {b b' : 𝔹} → b || b' ≡ tt → b ≡ tt ⊎ b' ≡ tt
||-split{tt}{tt} p = inj₁ refl
||-split{tt}{ff} p = inj₁ refl
||-split{ff}{tt} p = inj₂ refl
||-split{ff}{ff} ()

𝔹-dec : ∀ (b : 𝔹) → b ≡ tt ⊎ b ≡ ff
𝔹-dec tt = inj₁ refl
𝔹-dec ff = inj₂ refl

&&-snd : {p1 p2 : 𝔹} → p1 && p2 ≡ tt → p2 ≡ tt
&&-snd{tt} p = p
&&-snd{ff} ()

&&-fst : {p1 p2 : 𝔹} → p1 && p2 ≡ tt → p1 ≡ tt
&&-fst{tt} p = refl
&&-fst{ff} ()

&&-combo : {p1 p2 : 𝔹} → p1 ≡ tt → p2 ≡ tt → p1 && p2 ≡ tt
&&-combo{tt} pr1 pr2 = pr2
&&-combo{ff} pr1 pr2 = 𝔹-contra pr1

&&-ff : ∀(b : 𝔹) → b && ff ≡ ff
&&-ff tt = refl
&&-ff ff = refl

not-not : ∀(b : 𝔹) → (~ ~ b) ≡ b
not-not tt = refl
not-not ff = refl


contrapos : ∀{b1 b2 : 𝔹} → (b1 ≡ ff → b2 ≡ ff) → b2 ≡ tt → b1 ≡ tt
contrapos{b1}{b2} u d with keep b1
contrapos{b1}{b2} u d | tt , p = p
contrapos{b1}{b2} u d | ff , p rewrite u p with d
contrapos{b1}{b2} u d | ff , p | ()

contrapos2 : ∀{b1 b2 : 𝔹} → (b1 ≡ tt → b2 ≡ tt) → b2 ≡ ff → b1 ≡ ff
contrapos2{b1}{b2} u d with keep b1
contrapos2{b1}{b2} u d | ff , p = p
contrapos2{b1}{b2} u d | tt , p rewrite u p with d
contrapos2{b1}{b2} u d | tt , p | ()