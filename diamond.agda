{- definition of the diamond property for relations, and proof
   that reflexive-transitive closure preserves that property -}

open import eq
open import product
open import sum
open import rel
open import rtc

module diamond where

square : ∀{A : Set}(r1 : Rel A)(r2 : Rel A)(r3 : Rel A)(r4 : Rel A) → Set
square{A} r1 r2 r3 r4 = ∀ {x y z : A} → r1 x y → r2 x z → Σi[ q ∈ A ] r3 y q ∧ r4 z q

commute : ∀{A : Set}(r1 : Rel A)(r2 : Rel A) → Set
commute r1 r2 = square r1 r2 r1 r2

diamond : ∀{A : Set}(r : Rel A) → Set
diamond r = commute r r

subcommute : ∀{A : Set}(r1 : Rel A)(r2 : Rel A) → Set
subcommute{A} r1 r2 = ∀ {x y z : A} → r1 x y → r2 x z → y ≡ z ∨ Σi[ q ∈ A ] r2 y q ∧ r1 z q

subdiamond : ∀{A : Set}(r : Rel A) → Set
subdiamond r = subcommute r r

confluent : ∀{A : Set}(r : Rel A) → Set
confluent r = diamond (r ⋆)

-- this is called the Strip Lemma in sources like Barendregt 
⋆strip : ∀{A : Set}{r : Rel A} → diamond r → {x y z : A} → r x y → (r ⋆) x z → Σi[ q ∈ A ] (r ⋆) y q ∧ r z q
⋆strip u p1 (⋆base p2) with u p1 p2
⋆strip u p1 (⋆base p2) | , r1 , r2 = , ⋆base r1 , r2
⋆strip u  p1 ⋆refl = , ⋆refl , p1
⋆strip u p1 (p2 ⋆trans p3) with ⋆strip u p1 p2
⋆strip u p1 (p2 ⋆trans p3) | , r1 , r2 with ⋆strip u r2 p3
⋆strip u p1 (p2 ⋆trans p3) | , r1 , r2 | , r1' , r2' = , r1 ⋆trans r1' , r2' 

-- reflexive-transitive closure preserves the diamond property
⋆diamond : ∀{A : Set}{r : Rel A} → diamond r → diamond (r ⋆)
⋆diamond u (⋆base p1) p2 with ⋆strip u p1 p2
⋆diamond u (⋆base p1) p2 | , r1 , r2 = , r1 , ⋆base r2
⋆diamond u  ⋆refl p2 = , p2 , ⋆refl
⋆diamond u (p1 ⋆trans p2) p3 with ⋆diamond u p1 p3
⋆diamond u (p1 ⋆trans p2) p3 | , r1 , r2 with ⋆diamond u p2 r1
⋆diamond u (p1 ⋆trans p2) p3 | , r1 , r2 | , r1' , r2' = , r1' , r2 ⋆trans r2'

{- this lemma is the abstract justification for the Tait--Martin-Löf proof:
   If we can find a relation r2 that is
     1. intermediate between r1 and r1 ⋆, and
     2. has the diamond property, then
   r1 is confluent. -}
mediator-diamond : ∀{A : Set}{r1 r2 : Rel A} → r1 ⊆ r2 → r2 ⊆ r1 ⋆ → diamond r2 → confluent r1
mediator-diamond sub1 sub2 di2 p1 p2  with ⋆diamond di2 (⋆mono sub1 p1) (⋆mono sub1 p2)
mediator-diamond sub1 sub2 di2 p1 p2 | , q1 , q2 = , ⋆idem (⋆mono sub2 q1) , ⋆idem (⋆mono sub2 q2)

