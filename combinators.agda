module combinators where

open import bool
open import bool-thms2
open import eq
open import nat
open import nat-thms
open import product
open import well-founded

data comb : Set where
  S : comb
  K : comb
  app : comb → comb → comb

size : comb → ℕ
size S = 1
size K = 1
size (app a b) = suc (size a + size b)

data _↝_ : comb → comb → Set where
  ↝K : (a b : comb) → (app (app K a) b) ↝ a
  ↝S : (a b c : comb) → (app (app (app S a) b) c) ↝ (app (app a c) (app b c))
  ↝Cong1 : {a a' : comb} (b : comb) → a ↝ a' → (app a b) ↝ (app a' b)
  ↝Cong2 : (a : comb) {b b' : comb} → b ↝ b' → (app a b) ↝ (app a b')

Sfree : comb → 𝔹
Sfree S = ff
Sfree K = tt
Sfree (app a b) = Sfree a && Sfree b

appK-wf : ∀ {b : comb} → Wf _↝_ b → Wf _↝_ (app K b)
appK-wf{b} (pfWf fb) = pfWf h
  where h : {y : comb} → (app K b) ↝ y → Wf _↝_ y
        h (↝Cong1 .b ())
        h (↝Cong2 .K u) = appK-wf (fb u)

Sfree-↝-size> : ∀{a b : comb} → Sfree a ≡ tt → a ↝ b → size a > size b ≡ tt
Sfree-↝-size> p (↝K a b) = ≤<-trans {size a} (≤+1 (size a) (size b))
                                   (<-iter-suc-trans 2 (size a + size b))
Sfree-↝-size> () (↝S a b c)
Sfree-↝-size> p (↝Cong1{a}{a'} b u) with &&-elim{Sfree a} p
Sfree-↝-size> p (↝Cong1{a}{a'} b u) | p1 , _ = <+mono2 {size a'} (Sfree-↝-size> p1 u) 
Sfree-↝-size> p (↝Cong2 a u) with &&-elim{Sfree a} p
Sfree-↝-size> p (↝Cong2 a u) | _ , p2 = <+mono1{size a} (Sfree-↝-size> p2 u)

↝-preserves-Sfree : ∀{a b : comb} → Sfree a ≡ tt → a ↝ b → Sfree b ≡ tt
↝-preserves-Sfree p (↝K a b) = fst (&&-elim p)
↝-preserves-Sfree () (↝S a b c)
↝-preserves-Sfree p (↝Cong1 b u) with &&-elim p
↝-preserves-Sfree p (↝Cong1 b u) | p1 , p2 = &&-intro (↝-preserves-Sfree p1 u) p2
↝-preserves-Sfree p (↝Cong2 a u) with &&-elim{Sfree a} p 
↝-preserves-Sfree p (↝Cong2 a u) | p1 , p2 = &&-intro p1 (↝-preserves-Sfree p2 u)

Sfree-comb : Set
Sfree-comb = Σ comb (λ a → Sfree a ≡ tt)

↝-Sfree-comb : Sfree-comb → Sfree-comb → Set
↝-Sfree-comb (a , _) (b , _) = a ↝ b

size-Sfree-comb : Sfree-comb → ℕ
size-Sfree-comb (a , _) = size a

preserves : ∀ {x y : Sfree-comb} → ↝-Sfree-comb x y → size-Sfree-comb x > size-Sfree-comb y ≡ tt
preserves{a , u}{b , _} p = Sfree-↝-size> u p

open measure{A = Sfree-comb} ↝-Sfree-comb (λ x y → x > y ≡ tt) size-Sfree-comb preserves

measure-decreases : ∀(a : Sfree-comb) → Wf ↝-Sfree-comb a
measure-decreases a = measure-> (wf-> (size-Sfree-comb a))

Sfree-terminatesh : ∀{a : comb}{p : Sfree a ≡ tt} → Wf ↝-Sfree-comb (a , p) →  Wf _↝_ a
Sfree-terminatesh{a}{p} (pfWf f) = pfWf h
  where h : {y : comb} → a ↝ y → Wf _↝_ y
        h{y} u = Sfree-terminatesh (f {y , ↝-preserves-Sfree p u} u)  

Sfree-terminates : ∀(a : comb) → Sfree a ≡ tt → Wf _↝_ a
Sfree-terminates a p = Sfree-terminatesh (measure-decreases (a , p))

