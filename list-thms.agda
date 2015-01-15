module list-thms where

open import bool
open import bool-thms
open import list
open import nat
open import nat-thms
open import logic


++[] : ∀{ℓ}{A : Set ℓ} → (l : 𝕃 A) → l ++ [] ≡ l
++[] [] = refl
++[] (x :: xs) rewrite ++[] xs = refl


++-assoc : ∀ {ℓ}{A : Set ℓ} (l1 : 𝕃 A)(l2 : 𝕃 A)(l3 : 𝕃 A) → 
          (l1 ++ l2) ++ l3 ≡ l1 ++ (l2 ++ l3)
++-assoc [] l2 l3 = refl
++-assoc (x :: xs) l2 l3 rewrite ++-assoc xs l2 l3 = refl


multi++-assoc : ∀{ℓ}{A : Set ℓ} → (Ls : 𝕃 (𝕃 A)) → (l0 : 𝕃 A) → (foldr _++_ [] Ls) ++ l0 ≡ (foldr _++_ [] (Ls ++ [ l0 ]))
multi++-assoc [] l' rewrite ++[] l' = refl
multi++-assoc (l :: ls) l' rewrite ++-assoc l (foldr _++_ [] ls) l' | multi++-assoc ls l' = refl


map-append : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → 
             (f : A → B) (l1 l2 : 𝕃 A) → 
             map f (l1 ++ l2) ≡ (map f l1) ++ (map f l2)
map-append f [] l2 = refl
map-append f (x :: xs) l2 rewrite map-append f xs l2 = refl

map-compose : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'}{C : Set ℓ''} → 
             (f : A → B) (g : B → C) (l : 𝕃 A) → 
             map g (map f l) ≡ map (λ x → g (f x)) l
map-compose f g [] = refl
map-compose f g (x :: xs) rewrite map-compose f g xs = refl

invert𝕃 : ∀{ℓ}{A : Set ℓ}{t : A}{ts : 𝕃 A} → t :: ts ≢ []
invert𝕃 ()

length-repeat : ∀{ℓ}{A : Set ℓ} (n : ℕ) (a : A) → length (repeat n a) ≡ n
length-repeat 0 a = refl
length-repeat (suc n) a rewrite length-repeat n a = refl

length-reverse-helper : ∀{ℓ}{A : Set ℓ}(h l : 𝕃 A) → 
                      length (reverse-helper h l) ≡ length h + length l
length-reverse-helper h [] rewrite +0 (length h) = refl
length-reverse-helper h (x :: xs) rewrite length-reverse-helper (x :: h) xs = sym (+suc (length h) (length xs))

length-reverse : ∀{ℓ}{A : Set ℓ}(l : 𝕃 A) → length (reverse l) ≡ length l
length-reverse l = length-reverse-helper [] l

=𝕃-refl : ∀{ℓ}{A : Set ℓ}{l1 : 𝕃 A} → (eq : A → A → 𝔹) → ((x y : A) → x ≡ y → eq x y ≡ tt) → =𝕃 eq l1 l1 ≡ tt
=𝕃-refl{l1 = []} eq rise = refl
=𝕃-refl{l1 = x :: xs} eq rise = &&-combo (rise x x refl) (=𝕃-refl{l1 = xs} eq rise)

≡𝕃-from-= : ∀{ℓ}{A : Set ℓ}{l1 l2 : 𝕃 A} → (eq : A → A → 𝔹) → ((x y : A) → eq x y ≡ tt → x ≡ y) → =𝕃 eq l1 l2 ≡ tt → l1 ≡ l2
≡𝕃-from-={l1 = []}{[]} eq drop p = refl
≡𝕃-from-={l1 = x :: xs}{[]} eq drop ()
≡𝕃-from-={l1 = []}{y :: ys} eq drop ()
≡𝕃-from-={l1 = x :: xs}{y :: ys} eq drop p rewrite ≡𝕃-from-={l1 = xs} eq drop (&&-snd{eq x y}{=𝕃 eq xs ys} p) |  drop x y (&&-fst p) = refl 

=𝕃-from-≡ : ∀{ℓ}{A : Set ℓ}{l1 l2 : 𝕃 A} → (eq : A → A → 𝔹) → ((x y : A) → x ≡ y → eq x y ≡ tt) → l1 ≡ l2  → =𝕃 eq l1 l2 ≡ tt
=𝕃-from-≡{l2 = l2} eq rise p rewrite p  = =𝕃-refl{l1 = l2} eq rise 

