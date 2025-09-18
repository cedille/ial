module list-thms where

-- see list-thms2 for more 

open import bool
open import bool-thms
open import bool-thms2
open import bool-relations
open import functions
open import list
open import nat
open import nat-thms
open import product-thms
open import logic

++[] : ∀{ℓ}{A : Set ℓ} → (l : 𝕃 A) → l ++ [] ≡ l
++[] [] = refl
++[] (x :: xs) rewrite ++[] xs = refl

++-assoc : ∀ {ℓ}{A : Set ℓ} (l1 l2 l3 : 𝕃 A) → 
           (l1 ++ l2) ++ l3 ≡ l1 ++ (l2 ++ l3)
++-assoc [] l2 l3 = refl
++-assoc (x :: xs) l2 l3 rewrite ++-assoc xs l2 l3 = refl

length-++ : ∀{ℓ}{A : Set ℓ}(l1 l2 : 𝕃 A) → 
            length (l1 ++ l2) ≡ (length l1) + (length l2)
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

foldr-append : ∀{ℓ₁ ℓ₂}{A : Set ℓ₁}{B : Set ℓ₂}{l₁ l₂ : 𝕃 (A → 𝕃 B)}{a : A}
  → (foldr (λ f → _++_ (f a)) [] l₁) ++ (foldr (λ f → _++_ (f a)) [] l₂) ≡ foldr (λ f → _++_ (f a)) [] (l₁ ++ l₂)
foldr-append {l₁ = []}{_}{a} = refl
foldr-append {l₁ = x :: l₁}{l₂}{a}
 rewrite
    ++-assoc (x a) (foldr (λ f → _++_ (f a)) [] l₁) (foldr (λ f → _++_ (f a)) [] l₂)
  | foldr-append {l₁ = l₁}{l₂}{a}
 = refl
 
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

concat-foldr : ∀{ℓ}{A : Set ℓ} → (ls : 𝕃 (𝕃 A)) → (l : 𝕃 A) → concat ls ++ l ≡ foldr _++_ l ls
concat-foldr [] l = refl
concat-foldr (l' :: ls) l rewrite ++-assoc l' (concat ls) l | concat-foldr ls l = refl

--concat-foldr (l' :: (l'' :: ls)) l rewrite ++-assoc l' (concat (l'' :: ls)) l | concat-foldr (l'' :: ls) l = refl

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

filter-++ : ∀{ℓ}{A : Set ℓ}(p : A → 𝔹)(l1 l2 : 𝕃 A) → filter p (l1 ++ l2) ≡ filter p l1 ++ filter p l2
filter-++ p [] l2 = refl
filter-++ p (x :: l1) l2 with p x 
filter-++ p (x :: l1) l2 | tt rewrite (filter-++ p l1 l2) = refl
filter-++ p (x :: l1) l2 | ff rewrite (filter-++ p l1 l2) = refl

remove-++ : ∀{ℓ}{A : Set ℓ}(eq : A → A → 𝔹)(a : A)(l1 l2 : 𝕃 A) → 
            remove eq a (l1 ++ l2) ≡ remove eq a l1 ++ remove eq a l2
remove-++ eq a l1 l2 = filter-++ (λ x → ~ (eq a x)) l1 l2

::-injective : ∀{ℓ}{A : Set ℓ}{x y : A}{xs ys : 𝕃 A} → 
               x :: xs ≡ y :: ys → x ≡ y ∧ xs ≡ ys
::-injective refl = refl , refl

concat-++ : ∀{ℓ}{A : Set ℓ}(ls1 ls2 : 𝕃 (𝕃 A)) → concat (ls1 ++ ls2) ≡ (concat ls1) ++ (concat ls2)
concat-++ [] ls2 = refl
concat-++ (l :: ls) ls2 rewrite concat-++ ls ls2 = sym (++-assoc l (concat ls) (concat ls2))

-- This holds as long as we have the equations p₁ and p₂.  We know
-- that these equations are consistant to adopt, because they are
-- equivalent up and an isomorphism, and hence, by univalence they are
-- consistent as equations.  The respective isomorphisms can be found
-- in products-thms.agda.
all-pred-append : ∀{X : Set}{f : X → Set}{l₁ l₂}
  → (p₁ : ∀{ℓ}{A : Set ℓ} → A ≡ (⊤ ∧ A))
  → (p₂ : ∀{ℓ}{A B C : Set ℓ} →  (A ∧ (B ∧ C)) ≡ ((A ∧ B) ∧ C))
  → all-pred f (l₁ ++ l₂) ≡ ((all-pred f l₁) ∧ (all-pred f l₂))
all-pred-append {l₁ = []} {l₂} p₁ p₂ = p₁
all-pred-append {X}{f}{x :: l₁} {l₂} p₁ p₂ rewrite all-pred-append {X}{f}{l₁ = l₁} {l₂} p₁ p₂ = p₂ 

map-proj-⊎₁ : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'} → (l : 𝕃 A) → 
                proj-⊎₁ {A = A}{B} (map inj₁ l) ≡ l
map-proj-⊎₁ [] = refl
map-proj-⊎₁ {A = A}{B} (x :: l) rewrite map-proj-⊎₁ {A = A}{B} l = refl

map-proj-⊎₂ : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'} → (l : 𝕃 B) → 
                proj-⊎₂ {A = A}{B} (map inj₂ l) ≡ l
map-proj-⊎₂ [] = refl
map-proj-⊎₂ {A = A}{B} (x :: l) rewrite map-proj-⊎₂ {A = A}{B} l = refl

map-proj-⊎₂-[] : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'} → (l : 𝕃 A) → 
                  proj-⊎₂ {A = A}{B} (map inj₁ l) ≡ []
map-proj-⊎₂-[] [] = refl
map-proj-⊎₂-[] {A = A}{B} (x :: l) rewrite map-proj-⊎₂-[] {A = A}{B} l = refl

map-proj-⊎₁-[] : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'} → (l : 𝕃 B) → 
                  proj-⊎₁ {A = A}{B} (map inj₂ l) ≡ []
map-proj-⊎₁-[] [] = refl
map-proj-⊎₁-[] {A = A}{B} (x :: l) rewrite map-proj-⊎₁-[] {A = A}{B} l = refl

is-empty-++ : ∀{ℓ}{A : Set ℓ}(l1 l2 : 𝕃 A) → is-empty (l1 ++ l2) ≡ is-empty l1 && is-empty l2
is-empty-++ [] l2 = refl
is-empty-++ (x :: l1) l2 = refl

is-empty-ff-length : ∀{ℓ}{A : Set ℓ}(l : 𝕃 A) → is-empty l ≡ ff → length l =ℕ 0 ≡ ff
is-empty-ff-length [] ()
is-empty-ff-length (x :: l) p = refl

list-all-append : ∀{ℓ}{A : Set ℓ}(p : A → 𝔹)(l l' : 𝕃 A) →
                  list-all p (l ++ l') ≡ list-all p l && list-all p l'
list-all-append p [] l' = refl
list-all-append p (x :: l) l' rewrite list-all-append p l l' | &&-assoc (p x) (list-all p l) (list-all p l') = refl

length-init : ∀ {A : Set}(x : A)(xs : 𝕃 A) →
              length (init (x :: xs) refl) ≡ length xs
length-init x [] = refl
length-init x (x₁ :: []) = refl
length-init x (x₁ :: x₂ :: xs) rewrite length-init x₂ xs = refl

list-all-filter : ∀{A : Set}{p q : A → 𝔹}(l : 𝕃 A) →
                   (∀ (a : A) → (p a) ≡ ff → (q a) ≡ tt) →
                   list-all q (filter p l) ≡ tt →
                   list-all q l ≡ tt
list-all-filter [] sub al = refl
list-all-filter{p = p} (x :: l) sub al with keep (p x)
list-all-filter{q = q} (x :: l) sub al | tt , r rewrite r with &&-elim{q x} al
list-all-filter (x :: l) sub al | tt , r | al1 , al2 rewrite al1 = list-all-filter l sub al2
list-all-filter (x :: l) sub al | ff , r rewrite r | (sub x r) = list-all-filter l sub al

list-all-sub : ∀{A : Set}{p q : A → 𝔹}(l : 𝕃 A) →
               (∀ (a : A) → (p a) ≡ tt → (q a) ≡ tt) →
               list-all p l ≡ tt →
               list-all q l ≡ tt
list-all-sub [] sub u = refl
list-all-sub {p = p}(x :: l) sub u with keep (p x)
list-all-sub {p = p} (x :: l) sub u | tt , r rewrite (sub x r) = list-all-sub l sub (&&-elim2{p x} u)
list-all-sub (x :: l) sub u | ff , r rewrite r with u
list-all-sub (x :: l) sub u | ff , r | ()               

list-all-&& : ∀{A : Set}{p q : A → 𝔹}(l : 𝕃 A) →
               list-all p l ≡ tt →
               list-all q l ≡ tt → 
               list-all (λ x → p x && q x) l ≡ tt
list-all-&& [] u v = refl
list-all-&&{p = p}{q} (x :: l) u v =
  &&-intro (&&-intro{p x} (&&-elim1 u) (&&-elim1 v))
           (list-all-&& l (&&-elim2 u) (&&-elim2 v))

lengthSplitAt : ∀{A : Set}(n : ℕ)(l pre suff : 𝕃 A) →
                splitAt n l ≡ (pre , suff) →
                length l ≡ length pre + length suff
lengthSplitAt zero [] pre suff u with ,inj u
lengthSplitAt zero [] pre suff u | (u1 , u2) rewrite sym u1 | sym u2 = refl
lengthSplitAt zero (x :: l) pre suff u with ,inj u
lengthSplitAt zero (x :: l) pre suff u | (u1 , u2) rewrite sym u2 | sym u1 = refl
lengthSplitAt (suc n) [] pre suff u with ,inj u
lengthSplitAt (suc n) [] pre suff u | (u1 , u2) rewrite sym u1 | sym u2 = refl
lengthSplitAt (suc n) (x :: l) pre suff u with keep (splitAt n l) 
lengthSplitAt (suc n) (x :: l) pre suff u | ((pre' , suff') , p) rewrite p | lengthSplitAt n l pre' suff' p with ,inj u 
lengthSplitAt (suc n) (x :: l) pre suff u | ((pre' , suff') , p) | (u1 , u2) rewrite sym u1 | sym u2 = refl

isSublist-refl : ∀{A : Set}{eq : A → A → 𝔹} → 
                 reflexive eq → {l : 𝕃 A} →
                 isSublist l l eq ≡ tt
isSublist-refl r {[]} = refl
isSublist-refl{A}{eq} r {x :: l} with isSublist-refl{A}{eq} r {l}
isSublist-refl{A}{eq} r {x :: l} | p rewrite r {x} = list-all-sub l (λ a u → ||-intro2{eq a x} u) p

sublist-refl : ∀{A : Set}{l : 𝕃 A} → sublist l l
sublist-refl p = p

list-in-++1 : ∀{A : Set}{x : A}{l1 l2 : 𝕃 A} →
              list-in x l1 →
              list-in x (l1 ++ l2)
list-in-++1 {A} {x} {y :: l1} {l2} (inj₁ r) = inj₁ r
list-in-++1 {A} {x} {y :: l1} {l2} (inj₂ p) = inj₂ (list-in-++1 p)

list-in-++ : ∀{A : Set}{x : A}{l1 l2 : 𝕃 A} →
              list-in x (l1 ++ l2) → 
              list-in x l1 ∨ list-in x l2
list-in-++ {A} {x} {[]} {l2} p = inj₂ p
list-in-++ {A} {x} {y :: l1} {l2} (inj₁ p) = inj₁ (inj₁ p)
list-in-++ {A} {x} {y :: l1} {l2} (inj₂ p) with list-in-++{l1 = l1} p 
list-in-++ {A} {x} {y :: l1} {l2} (inj₂ p) | inj₁ q = inj₁ (inj₂ q)
list-in-++ {A} {x} {y :: l1} {l2} (inj₂ p) | inj₂ q = inj₂ q

sublist-++1 : ∀{A : Set}{l1 l2 l : 𝕃 A} →
             sublist (l1 ++ l2) l →
             sublist l1 l 
sublist-++1{A}{l1}{l2}{l} S {x} p = S (list-in-++1 p)

list-in-++2 : ∀{A : Set}{x : A}{l1 l2 : 𝕃 A} →
              list-in x l2 →
              list-in x (l1 ++ l2)
list-in-++2 {A} {x} {[]} {l2} p = p
list-in-++2 {A} {x} {y :: l1} {l2} p = inj₂ (list-in-++2 p)

sublist-++2 : ∀{A : Set}{l1 l2 l : 𝕃 A} →
             sublist (l1 ++ l2) l →
             sublist l2 l 
sublist-++2{A}{l1}{l2}{l} S {x} p = S (list-in-++2 p)

list-member-sub : ∀{A : Set}{eq : A → A → 𝔹}{a : A}{l1 l2 : 𝕃 A} →
                  computational-equality eq → 
                  list-member eq a l1 ≡ tt →
                  isSublist l1 l2 eq ≡ tt → 
                  list-member eq a l2 ≡ tt
list-member-sub {eq = eq}{a}{x :: l1}{l2} e mem sub with ||-elim{eq a x} mem | &&-elim{list-member eq x l2} sub 
list-member-sub {eq = _} {_} {x :: l1} e mem sub | inj₁ p | u1 , u2 rewrite e p = u1
list-member-sub {eq = _} {a} {x :: l1} {l2} e mem sub | inj₂ p | u1 , u2 = list-member-sub{a = a}{l1}{l2} e p u2

list-member-sub-ff : ∀{A : Set}{eq : A → A → 𝔹}{a : A}{l1 l2 : 𝕃 A} →
                     computational-equality eq → 
                     isSublist l1 l2 eq ≡ tt → 
                     list-member eq a l2 ≡ ff →
                     list-member eq a l1 ≡ ff
list-member-sub-ff{A}{eq}{a}{l1}{l2} ceq sub =
  contrapos2{list-member eq a l1}{list-member eq a l2} λ m → list-member-sub{a = a}{l1}{l2} ceq m sub
  

isSublist-++1 : ∀{A : Set}{eq : A → A → 𝔹}{l1 l2 : 𝕃 A} →
                reflexive eq → 
                isSublist l1 (l1 ++ l2) eq ≡ tt
isSublist-++1 {A} {eq} {[]} {l2} _ = refl
isSublist-++1 {A} {eq} {x :: l1} {l2} r with isSublist-++1{A}{eq}{l1}{l2} r
isSublist-++1 {A} {eq} {x :: l1} {l2} r | ih rewrite r {x} =
  list-all-sub{p = λ a → list-member eq a (l1 ++ l2)} l1 (λ a u → ||-intro2 u) ih

isSublist-++2 : ∀{A : Set}{eq : A → A → 𝔹}{l1 l2 l2' : 𝕃 A} →
                reflexive eq →
                isSublist l2 l2' eq ≡ tt → 
                isSublist l2 (l1 ++ l2') eq ≡ tt
isSublist-++2 {A} {eq} {[]} {l2} r p = p
isSublist-++2 {A} {eq} {x :: l1} {l2} {l2'} r p with isSublist-++2{A}{eq}{l1}{l2}{l2'} r p
isSublist-++2 {A} {eq} {x :: l1} {l2} {l2'} r p | ih rewrite r {x} = 
 list-all-sub{p = λ a → list-member eq a (l1 ++ l2')} l2 (λ a u → ||-intro2 u) ih

isSublist-++-cong : ∀{A : Set}{eq : A → A → 𝔹}{l1 l2 l3 : 𝕃 A} →
                    reflexive eq → 
                    isSublist l2 l3 eq ≡ tt → 
                    isSublist (l1 ++ l2) (l1 ++ l3) eq ≡ tt
isSublist-++-cong {A} {eq} {[]} {l2} r p = p
isSublist-++-cong {A} {eq} {x :: l1} {l2} {l3} r p with isSublist-++-cong{A}{eq}{l1}{l2}{l3} r p 
isSublist-++-cong {A} {eq} {x :: l1} {l2} {l3} r p | u rewrite r {x} =
  list-all-sub{A}{λ a → list-member eq a (l1 ++ l3)} (l1 ++ l2) (λ a u → ||-intro2 u) u

isSublist-++-merge : ∀{A : Set}{eq : A → A → 𝔹}{l1 l1' l2 l2' : 𝕃 A} →
                      computational-equality eq → 
                      reflexive eq → 
                      isSublist l1 l1' eq ≡ tt →
                      isSublist l2 l2' eq ≡ tt →                       
                      isSublist (l1 ++ l2) (l1' ++ l2') eq ≡ tt
isSublist-++-merge{eq = eq} {[]} {l1'}{l2}{l2'} _ r s1 s2 = isSublist-++2{eq = eq}{l1 = l1'}{l2 = l2}{l2'} r s2
isSublist-++-merge{eq = eq} {x :: l1} {l1'} ceq r s1 s2 with &&-elim {list-member eq x l1'} s1
isSublist-++-merge{eq = eq} {x :: l1} {l1'}{l2}{l2'} ceq r s1 s2 | s1a , s1b
  rewrite isSublist-++-merge{eq = eq}{l1}{l1'}{l2}{l2'} ceq r s1b s2 |
          list-member-sub{eq = eq}{x}{l1'}{l1' ++ l2'} ceq s1a (isSublist-++1 {eq = eq} {l1'} {l2'} r) = refl

isSublist-trans : ∀{A : Set}{eq : A → A → 𝔹}{l1 l2 l3 : 𝕃 A} →
                  computational-equality eq → 
                  isSublist l1 l2 eq ≡ tt →
                  isSublist l2 l3 eq ≡ tt →
                  isSublist l1 l3 eq ≡ tt
isSublist-trans {eq = eq} {[]} {l2} {l3} _ s12 s23 = refl
isSublist-trans {eq = eq} {x :: l1} {l2} {l3} ceq s12 s23 with &&-elim {list-member eq x l2} s12
isSublist-trans {eq = eq} {x :: l1} {l2} {l3} ceq s12 s23 | p1 , p2
  rewrite list-member-sub{eq = eq}{x}{l2}{l3} ceq p1 s23 = isSublist-trans{eq = eq}{l1}{l2}{l3} ceq p2 s23

isSublist-++1l : ∀{A : Set}{eq : A → A → 𝔹}{l1 l2 l3 : 𝕃 A} →
                 isSublist (l1 ++ l2) l3 eq ≡ tt → 
                 isSublist l1 l3 eq ≡ tt
isSublist-++1l {A} {eq} {[]} {l2} {l3} s = refl
isSublist-++1l {A} {eq} {x :: l1} {l2} {l3} s with &&-elim{list-member eq x l3} s
isSublist-++1l {A} {eq} {x :: l1} {l2} {l3} s | s1 , s2 = &&-intro{list-member eq x l3} s1 (isSublist-++1l{A}{eq}{l1}{l2}{l3} s2)

isSublist-++2l : ∀{A : Set}{eq : A → A → 𝔹}{l1 l2 l3 : 𝕃 A} →
                 isSublist (l1 ++ l2) l3 eq ≡ tt → 
                 isSublist l2 l3 eq ≡ tt
isSublist-++2l {A} {eq} {[]} {l2} {l3} s = s
isSublist-++2l {A} {eq} {x :: l1} {l2} {l3} s with &&-elim{list-member eq x l3} s
isSublist-++2l {A} {eq} {x :: l1} {l2} {l3} s | s1 , s2 = isSublist-++2l{A}{eq}{l1}{l2}{l3} s2

list-member-list-all-ff : ∀{A : Set}{eq : A → A → 𝔹}{z : A}{l : 𝕃 A} → 
                           list-all (λ x → ~ (eq z x)) l ≡ tt →
                           list-member eq z l ≡ ff
list-member-list-all-ff {l = []} p = refl
list-member-list-all-ff {eq = eq}{z}{x :: l} p with eq z x
list-member-list-all-ff {eq = _} {_} {x :: l} p | ff = list-member-list-all-ff{l = l} p

list-in-remove : ∀{A : Set}{eq : A → A → 𝔹}{x y : A}{l : 𝕃 A} →
                  computational-equality eq →
                  reflexive eq →                   
                  eq x y ≡ ff → 
                  list-in x l →
                  list-in x (remove eq y l)
list-in-remove {eq = eq}{x}{y}{z :: l} ceq rf e i with keep (eq y z)
list-in-remove {eq = eq}{x}{y}{z :: l} ceq rf e i | tt , p rewrite p with keep (eq x z) 
list-in-remove {eq = eq}{x}{y}{z :: l} ceq rf e i | tt , p | tt , q rewrite ceq p | ceq q | rf{z} with e
list-in-remove {eq = eq}{x}{y}{z :: l} ceq rf e i | tt , p | tt , q | ()
list-in-remove {eq = eq}{x}{y}{z :: l} ceq rf e (inj₁ i) | tt , p | ff , q rewrite i | rf{z} with q 
list-in-remove {eq = eq}{x}{y}{z :: l} ceq rf e (inj₁ i) | tt , p | ff , q | () 
list-in-remove {eq = eq}{x}{y}{z :: l} ceq rf e (inj₂ i) | tt , p | ff , q = list-in-remove ceq rf e i
list-in-remove {eq = eq}{x}{y}{z :: l} ceq rf e (inj₁ i) | ff , p rewrite p = inj₁ i
list-in-remove {eq = eq}{x}{y}{z :: l} ceq rf e (inj₂ i) | ff , p rewrite p = inj₂ (list-in-remove ceq rf e i)

sublist-remove : ∀{A : Set}{eq : A → A → 𝔹}{l1 l2 : 𝕃 A}{a : A} →
                  computational-equality eq →
                  reflexive eq →
                  sublist (remove eq a l1) l2 →
                  sublist l1 (a :: l2)
sublist-remove {l1 = []} _ _ S ()
sublist-remove {eq = eq}{x :: l1}{a = a} ceq rf S p with keep (eq a x)
sublist-remove {eq = eq}{l1 = x :: l1}{a = a} ceq rf S p | tt , q rewrite ceq q with p 
sublist-remove {eq = eq}{l1 = x :: l1}{a = a} ceq rf S p | tt , q | inj₁ p' = inj₁ p'
sublist-remove {eq = eq}{l1 = x :: l1}{a = a} ceq rf S {y} p | tt , q | inj₂ p' rewrite rf{a} with keep (eq y a) 
sublist-remove {eq = eq}{l1 = x :: l1}{a = a} ceq rf S {y} p | tt , q | inj₂ p' | tt , w rewrite ceq q | ceq w = inj₁ (ceq (rf{x}))
sublist-remove {eq = eq}{l1 = x :: l1}{a = a} ceq rf S {y} p | tt , q | inj₂ p' | ff , w rewrite rf{x} | ceq q =
  inj₂ (S (list-in-remove{eq = eq} ceq rf w p'))
sublist-remove {eq = eq}{l1 = x :: l1}{a = a} ceq rf S (inj₁ p) | ff , q rewrite p | q  = inj₂ (S (inj₁ refl))
sublist-remove {eq = eq}{l1 = x :: l1}{a = a} ceq rf S {y} (inj₂ p) | ff , q rewrite q = sublist-remove ceq rf (λ p → S (inj₂ p)) p

list-in-remove2 : ∀{A : Set}{eq : A → A → 𝔹}{x y : A}{l : 𝕃 A} →
                  list-in x (remove eq y l) →
                  eq y x ≡ ff 
list-in-remove2 {eq = eq}{x}{y}{z :: l} i with keep (eq y z)
list-in-remove2 {eq = eq}{x}{y}{z :: l} i | tt , p rewrite p = list-in-remove2{eq = eq}{l = l} i
list-in-remove2 {eq = eq}{x}{y}{z :: l} i | ff , p rewrite p with i
list-in-remove2 {eq = eq}{x}{y}{z :: l} i | ff , p | inj₁ refl = p
list-in-remove2 {eq = eq}{x}{y}{z :: l} i | ff , p | inj₂ u = list-in-remove2{eq = eq}{l = l} u

list-in-remove3 : ∀{A : Set}{eq : A → A → 𝔹}{x y : A}{l : 𝕃 A} →
                  computational-equality eq →
                  list-in x (remove eq y l) →
                  list-in x l
list-in-remove3 {A} {eq} {x} {y} {z :: l} ceq L with keep (eq x z)
list-in-remove3 {A} {eq} {x} {y} {z :: l} ceq L | tt , p = inj₁ (ceq p)
list-in-remove3 {A} {eq} {x} {y} {z :: l} ceq L | ff , p with eq y z
list-in-remove3 {A} {eq} {x} {y} {z :: l} ceq L | ff , p | tt = inj₂ (list-in-remove3 ceq L)
list-in-remove3 {A} {eq} {x} {y} {z :: l} ceq L | ff , p | ff with L
list-in-remove3 {A} {eq} {x} {y} {z :: l} ceq L | ff , p | ff | inj₁ r = inj₁ r
list-in-remove3 {A} {eq} {x} {y} {z :: l} ceq L | ff , p | ff | inj₂ r = inj₂ (list-in-remove3 ceq r)