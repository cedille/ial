module list-thms where

open import bool
open import bool-thms
open import compose
open import list
open import nat
open import nat-thms
open import product-thms
open import logic

++[] : ∀{ℓ}{A : Set ℓ} → (l : 𝕃 A) → l ++ [] ≡ l
++[] [] = refl
++[] (x :: xs) rewrite ++[] xs = refl

++-assoc : ∀ {ℓ}{A : Set ℓ} (l1 : 𝕃 A)(l2 : 𝕃 A)(l3 : 𝕃 A) → 
          (l1 ++ l2) ++ l3 ≡ l1 ++ (l2 ++ l3)
++-assoc [] l2 l3 = refl
++-assoc (x :: xs) l2 l3 rewrite ++-assoc xs l2 l3 = refl

length-++ : ∀{ℓ}{A : Set ℓ}(l1 l2 : 𝕃 A) → length (l1 ++ l2) ≡ (length l1) + (length l2)
length-++ [] l2 = refl
length-++ (h :: t) l2 rewrite length-++ t l2 = refl

map-append : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → 
             (f : A → B) (l1 l2 : 𝕃 A) → 
             map f (l1 ++ l2) ≡ (map f l1) ++ (map f l2)
map-append f [] l2 = refl
map-append f (x :: xs) l2 rewrite map-append f xs l2 = refl

map-compose : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'}{C : Set ℓ''} → 
             (f : B → C) (g : A → B) (l : 𝕃 A) → 
             map f (map g l) ≡ map (f ∘ g) l
map-compose f g [] = refl
map-compose f g (x :: xs) rewrite map-compose f g xs = refl

invert𝕃 : ∀{ℓ}{A : Set ℓ}{t : A}{ts : 𝕃 A} → t :: ts ≢ []
invert𝕃 ()

length-repeat : ∀{ℓ}{A : Set ℓ} (n : ℕ) (a : A) → length (repeat n a) ≡ n
length-repeat 0 a = refl
length-repeat (suc n) a rewrite length-repeat n a = refl

map-repeat : ∀ {ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'}(n : ℕ)(a : A)(f : A → B) → map f (repeat n a) ≡ repeat n (f a)
map-repeat 0 a f = refl
map-repeat (suc x) a f rewrite map-repeat x a f = refl

length-map : ∀{ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B)(l : 𝕃 A) → length (map f l) ≡ length l
length-map f [] = refl
length-map f (head :: tail) rewrite length-map f tail = refl

length-reverse-helper : ∀{ℓ}{A : Set ℓ}(h l : 𝕃 A) → 
                      length (reverse-helper h l) ≡ length h + length l
length-reverse-helper h [] rewrite +0 (length h) = refl
length-reverse-helper h (x :: xs) rewrite length-reverse-helper (x :: h) xs = sym (+suc (length h) (length xs))

length-reverse : ∀{ℓ}{A : Set ℓ}(l : 𝕃 A) → length (reverse l) ≡ length l
length-reverse l = length-reverse-helper [] l

reverse-++h : ∀{ℓ}{A : Set ℓ}(l1 l2 : 𝕃 A) → reverse-helper l1 l2 ≡ reverse-helper [] l2 ++ l1
reverse-++h l1 [] = refl
reverse-++h l1 (x :: xs) rewrite reverse-++h (x :: l1) xs | reverse-++h (x :: []) xs | ++-assoc (reverse xs) (x :: []) l1 = refl

reverse-++ : ∀{ℓ}{A : Set ℓ}(l1 l2 : 𝕃 A) → reverse(l1 ++ l2) ≡ reverse(l2) ++ reverse(l1)
reverse-++ [] l2 rewrite ++[] (reverse l2) = refl
reverse-++ (x :: xs) l2 rewrite reverse-++h (x :: []) (xs ++ l2) | reverse-++ xs l2 | ++-assoc (reverse l2) (reverse xs) (x :: []) | sym (reverse-++h (x :: []) xs) = refl 

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

multi++-assoc : ∀{ℓ}{A : Set ℓ} → (Ls : 𝕃 (𝕃 A)) → (l0 : 𝕃 A) → (foldr _++_ [] Ls) ++ l0 ≡ (foldr _++_ [] (Ls ++ [ l0 ]))
multi++-assoc [] l' rewrite ++[] l' = refl
multi++-assoc (l :: ls) l' rewrite ++-assoc l (foldr _++_ [] ls) l' | multi++-assoc ls l' = refl

longer-trans : ∀{ℓ}{A : Set ℓ}(l1 l2 l3 : 𝕃 A) → 
                l1 longer l2 ≡ tt →
                l2 longer l3 ≡ tt →
                l1 longer l3 ≡ tt
longer-trans [] l2 l3 () q 
longer-trans (x :: l1) [] l3 p ()
longer-trans (x :: l1) (x₁ :: l2) [] p q = refl
longer-trans (x :: l1) (x₁ :: l2) (x₂ :: l3) p q = longer-trans l1 l2 l3 p q

filter-idem : ∀{ℓ}{A : Set ℓ}(p : A → 𝔹)(l : 𝕃 A) →
              (filter p (filter p l)) ≡ (filter p l)
filter-idem p [] = refl
filter-idem p (x :: l) with keep (p x)
filter-idem p (x :: l) | tt , p' rewrite p' | p' | filter-idem p l = refl
filter-idem p (x :: l) | ff , p' rewrite p' = filter-idem p l

length-filter : ∀{ℓ}{A : Set ℓ}(p : A → 𝔹)(l : 𝕃 A) → 
                length (filter p l) ≤ length l ≡ tt
length-filter p [] = refl
length-filter p (x :: l) with p x
length-filter p (x :: l) | tt = length-filter p l
length-filter p (x :: l) | ff = 
  ≤-trans{length (filter p l)} (length-filter p l) (≤-suc (length l))

::-injective : ∀{ℓ}{A : Set ℓ}{x y : A}{xs ys : 𝕃 A} → 
               x :: xs ≡ y :: ys → x ≡ y ∧ xs ≡ ys
::-injective refl = refl , refl

concat-thm : ∀{ℓ}{A : Set ℓ}(ls1 ls2 : 𝕃 (𝕃 A)) → concat (ls1 ++ ls2) ≡ (concat ls1) ++ (concat ls2)
concat-thm [] ls2 = refl
concat-thm (ls1 :: ls2) ls3 rewrite concat-thm ls2 ls3 = sym (++-assoc ls1 (concat ls2) (concat ls3))