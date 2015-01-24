module bool-thms2 where

open import bool
open import eq
open import product
open import sum

ff-imp : ∀ (b : 𝔹) → ff imp b ≡ tt
ff-imp ff = refl
ff-imp tt = refl

imp-tt : ∀ (b : 𝔹) → b imp tt ≡ tt
imp-tt ff = refl
imp-tt tt = refl

imp-same : ∀ (b : 𝔹) → b imp b ≡ tt
imp-same ff = refl
imp-same tt = refl

&&-contra : ∀ (b : 𝔹) → b && ~ b ≡ ff
&&-contra ff = refl
&&-contra tt = refl

&&-comm : ∀ (b1 b2 : 𝔹) → b1 && b2 ≡ b2 && b1
&&-comm ff ff = refl
&&-comm ff tt = refl
&&-comm tt ff = refl
&&-comm tt tt = refl

||-comm : ∀ (b1 b2 : 𝔹) → b1 || b2 ≡ b2 || b1
||-comm ff ff = refl
||-comm ff tt = refl
||-comm tt ff = refl
||-comm tt tt = refl

&&-assoc : ∀ (b1 b2 b3 : 𝔹) → b1 && (b2 && b3) ≡ (b1 && b2) && b3
&&-assoc ff _ _ = refl
&&-assoc tt _ _ = refl

||-assoc : ∀ (b1 b2 b3 : 𝔹) → b1 || (b2 || b3) ≡ (b1 || b2) || b3
||-assoc tt _ _ = refl
||-assoc ff _ _ = refl

~-over-&& : ∀ (b1 b2 : 𝔹) → ~ ( b1 && b2 ) ≡ (~ b1 || ~ b2)
~-over-&& tt _ = refl
~-over-&& ff _ = refl

~-over-|| : ∀ (b1 b2 : 𝔹) → ~ ( b1 || b2 ) ≡ (~ b1 && ~ b2)
~-over-|| tt _ = refl
~-over-|| ff _ = refl

&&-over-||-l : ∀ (a b c : 𝔹) → a && (b || c) ≡ (a && b) || (a && c)
&&-over-||-l tt _ _ = refl
&&-over-||-l ff _ _ = refl 

&&-over-||-r : ∀ (a b c : 𝔹) → (a || b) && c ≡ (a && c) || (b && c)
&&-over-||-r tt tt tt = refl
&&-over-||-r tt tt ff = refl
&&-over-||-r tt ff tt = refl
&&-over-||-r tt ff ff = refl
&&-over-||-r ff tt tt = refl
&&-over-||-r ff tt ff = refl
&&-over-||-r ff ff tt = refl
&&-over-||-r ff ff ff = refl

||-over-&&-l : ∀ (a b c : 𝔹) → a || (b && c) ≡ (a || b) && (a || c)
||-over-&&-l tt _ _ = refl
||-over-&&-l ff _ _ = refl 

||-over-&&-r : ∀ (a b c : 𝔹) → (a && b) || c ≡ (a || c) && (b || c)
||-over-&&-r tt _ _ = refl
||-over-&&-r ff _ ff = refl
||-over-&&-r ff tt tt = refl
||-over-&&-r ff ff tt = refl

imp-to-|| : ∀ (b1 b2 : 𝔹) → (b1 imp b2) ≡ (~ b1 || b2)
imp-to-|| ff _ = refl
imp-to-|| tt _ = refl

imp-mp : ∀ {b b' : 𝔹} → b imp b' ≡ tt → b ≡ tt → b' ≡ tt 
imp-mp {tt} {tt} p refl = refl
imp-mp {ff} {ff} p q = q
imp-mp {tt} {ff} p q = p
imp-mp {ff} {tt} p q = refl

&&-cong₁ : ∀ {b1 b1' b2 : 𝔹} → b1 ≡ b1' → b1 && b2 ≡ b1' && b2
&&-cong₁ refl = refl

&&-cong₂ : ∀ {b1 b2 b2' : 𝔹} → b2 ≡ b2' → b1 && b2 ≡ b1 && b2'
&&-cong₂ refl = refl 

&&-intro : ∀ {b1 b2 : 𝔹} → b1 ≡ tt → b2 ≡ tt → b1 && b2 ≡ tt
&&-intro{tt}{tt} _ _ = refl
&&-intro{tt}{ff} _ ()
&&-intro{ff}{tt} () _
&&-intro{ff}{ff} () _

&&-elim : ∀ {b1 b2 : 𝔹} → b1 && b2 ≡ tt → b1 ≡ tt ∧ b2 ≡ tt 
&&-elim{tt}{tt} _ = refl , refl
&&-elim{ff}{_} ()
&&-elim{tt}{ff} ()

~-cong : ∀ {b b' : 𝔹} → b ≡ b' → ~ b ≡ ~ b'
~-cong refl = refl

ite-cong₁ : ∀{ℓ}{A : Set ℓ} {b b' : 𝔹}(x y : A) → b ≡ b' → (if b then x else y) ≡ (if b' then x else y)
ite-cong₁ x y refl = refl

ite-cong₂ : ∀{ℓ}{A : Set ℓ} (b : 𝔹){x x' : A}(y : A) → x ≡ x' → (if b then x else y) ≡ (if b then x' else y)
ite-cong₂ b y refl = refl

ite-cong₃ : ∀{ℓ}{A : Set ℓ} (b : 𝔹)(x : A){y y' : A} → y ≡ y' → (if b then x else y) ≡ (if b then x else y')
ite-cong₃ b x refl = refl

&&-split : ∀ {b b' : 𝔹} → b || b' ≡ ff → b ≡ ff ⊎ b' ≡ ff
&&-split {tt} ()
&&-split {ff}{tt} ()
&&-split {ff}{ff} p = inj₁ refl

imp-ff : ∀ (b : 𝔹) → b imp ff ≡ ~ b
imp-ff tt = refl
imp-ff ff = refl

tt-imp : ∀ (b : 𝔹) → tt imp b ≡ b
tt-imp tt = refl
tt-imp ff = refl

ff-xor : ∀ (b : 𝔹) → ff xor b ≡ b
ff-xor tt = refl
ff-xor ff = refl

tt-xor : ∀ (b : 𝔹) → tt xor b ≡ ~ b
tt-xor tt = refl
tt-xor ff = refl

~-xor-distrb : ∀ (a b : 𝔹) → ~ (a xor b) ≡ ~ a xor b
~-xor-distrb tt tt = refl
~-xor-distrb tt ff = refl
~-xor-distrb ff tt = refl
~-xor-distrb ff ff = refl

xor-distrib-&& : ∀ (x y : 𝔹) → x xor (y && x) ≡ ~ y && x
xor-distrib-&& tt tt = refl
xor-distrib-&& tt ff = refl
xor-distrib-&& ff tt = refl
xor-distrib-&& ff ff = refl
