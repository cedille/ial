module kripke-semantics where

open import level
open import bool
open import empty
open import eq
open import list
open import list-thms
open import nat
open import product
open import relations
open import sum
open import unit

data formula : Set where
  $_ : ℕ → formula
  True : formula
  Implies : formula → formula → formula
  And : formula → formula → formula

record model   : Set1 where
  field W         : Set -- a set of worlds
        R         : W → W → Set
        preorderR : preorder R -- a proof that R is a preorder (reflexive and transitive)
        V         : W → ℕ → Set -- a valuation telling whether atomic formula i is true or false in a given world
        monoR     : ∀ { w w' } → R w w' → ∀ { i } → V w i → V w' i
  reflR : reflexive R
  reflR = fst preorderR
  transR : transitive R
  transR = snd preorderR

open model

_,_⊨_ : ∀(k : model) → W k → formula → Set

k , w ⊨ ($ x) = V k w x
k , w ⊨ True = ⊤
k , w ⊨ Implies f1 f2 = ∀ {w' : W k} → R k w w' → k , w' ⊨ f1 → k , w' ⊨ f2
k , w ⊨ And f1 f2 = k , w ⊨ f1 ∧ k , w ⊨ f2

mono⊨ : ∀{k : model}{w1 w2 : W k}{f : formula} → 
         R k w1 w2 → 
         k , w1 ⊨ f → 
         k , w2 ⊨ f
mono⊨{k} {f = $ x} r p = monoR k r p 
mono⊨{k} {f = True} r p = triv
mono⊨{k} {f = Implies f1 f2} r p r' p' = p (transR k r r') p'
mono⊨{k} {f = And f1 f2} r (p1 , p2) = mono⊨{f = f1} r p1 , mono⊨{f = f2} r p2

⊨_ : formula → Set1
⊨ f = ∀{k : model}{w : W k} → k , w ⊨ f

S-formula : formula → formula → formula → formula 
S-formula f1 f2 f3 = Implies (Implies f1 (Implies f2 f3)) (Implies (Implies f1 f2) (Implies f1 f3))

ctxt : Set
ctxt = 𝕃 formula

data _⊢_ : ctxt → formula → Set where
  assume : ∀{Γ f} → (f :: Γ) ⊢ f
  weaken : ∀{Γ f f'} → Γ ⊢ f → (f' :: Γ) ⊢ f
  ImpliesI : ∀{Γ f1 f2} → (f1 :: Γ) ⊢ f2 → Γ ⊢ (Implies f1 f2)
  ImpliesE : ∀{Γ f1 f2} → Γ ⊢ (Implies f1 f2) → Γ ⊢ f1 → Γ ⊢ f2
  TrueI : ∀ {Γ} → Γ ⊢ True
  AndI : ∀{Γ f1 f2} → Γ ⊢ f1 → Γ ⊢ f2 → Γ ⊢ (And f1 f2)
  AndE : ∀(b : 𝔹){Γ f1 f2} → Γ ⊢ (And f1 f2) → Γ ⊢ (if b then f1 else f2)

ctxt∧ : ctxt → formula
ctxt∧ [] = True
ctxt∧ (f :: Γ) = And f (ctxt∧ Γ)

Soundness : ∀{Γ : ctxt}{f : formula} → Γ ⊢ f → ∀{k : model}{w : W k} → k , w ⊨ ctxt∧ Γ → k , w ⊨ f
Soundness assume g = fst g
Soundness (weaken p) g = Soundness p (snd g)
Soundness{Γ} (ImpliesI p) {k} g r u' = Soundness p (u' , mono⊨ {k}{f = ctxt∧ Γ} r g)
Soundness (ImpliesE p p') {k} g = (Soundness p g) (reflR k) (Soundness p' g)
Soundness TrueI g = triv
Soundness (AndI p p') g = (Soundness p g , Soundness p' g)
Soundness (AndE tt p) g = fst (Soundness p g)
Soundness (AndE ff p) g = snd (Soundness p g)

data _≼_ : 𝕃 formula → 𝕃 formula → Set where 
  ≼-refl : ∀ {Γ} → Γ ≼ Γ
  ≼-cons : ∀ {Γ Γ' f} → Γ ≼ Γ' → Γ ≼ (f :: Γ')
    
≼-trans : ∀ {Γ Γ' Γ''} → Γ ≼ Γ' → Γ' ≼ Γ'' → Γ ≼ Γ''
≼-trans u ≼-refl = u
≼-trans u (≼-cons u') = ≼-cons (≼-trans u u') 

≼-extend : ∀{f}{Γ} → Γ ≼ (f :: Γ)
≼-extend = ≼-cons ≼-refl

weaken≼ : ∀ {Γ Γ'}{f : formula} → Γ ≼ Γ' → Γ ⊢ f → Γ' ⊢ f
weaken≼ ≼-refl p = p
weaken≼ (≼-cons d) p = weaken (weaken≼ d p)

U : model
U = record { W = ctxt ;
             R = _≼_ ;
             preorderR = ≼-refl , ≼-trans ;
             V = λ Γ n → Γ ⊢ $ n ;
             monoR = λ d p → weaken≼ d p }

CompletenessU : ∀{f : formula}{Γ : W U} → U , Γ ⊨ f → Γ ⊢ f 
SoundnessU : ∀{f : formula}{Γ : W U} → Γ ⊢ f → U , Γ ⊨ f
CompletenessU {$ x} u = u
CompletenessU {True} u = TrueI
CompletenessU {Implies f f'}{Γ} u = 
  ImpliesI 
    (CompletenessU {f'} 
      (u (≼-cons ≼-refl) (SoundnessU {f} (assume {Γ}))))
CompletenessU {And f f'} u = AndI (CompletenessU{f} (fst u)) (CompletenessU{f'} (snd u))
SoundnessU {$ x} p = p
SoundnessU {True} p = triv
SoundnessU {Implies f f'} p r u = SoundnessU (ImpliesE (weaken≼ r p) (CompletenessU {f} u))
SoundnessU {And f f'} p = SoundnessU{f} (AndE tt p) , SoundnessU{f'} (AndE ff p)

nbe : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A
nbe {Γ} p = CompletenessU (SoundnessU p)

module tests where

  -- here we see several proofs which normalize to just TrueI using the nbe function

  a : [] ⊢ True
  a = AndE tt (AndI TrueI TrueI)

  a' : [] ⊢ True
  a' = nbe a

  b : [] ⊢ True
  b = ImpliesE (ImpliesE (ImpliesI (ImpliesI (assume))) TrueI) TrueI

  b' : [] ⊢ True
  b' = nbe a

