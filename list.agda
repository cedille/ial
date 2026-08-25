module list where

open import level
open import bool
open import eq
open import maybe
open import nat
open import unit
open import product
open import empty
open import sum

----------------------------------------------------------------------
-- datatypes
----------------------------------------------------------------------

data 𝕃 {ℓ} (A : Set ℓ) : Set ℓ where
  [] : 𝕃 A
  _::_ : (x : A) (xs : 𝕃 A) → 𝕃 A

{-# BUILTIN LIST 𝕃 #-}

list = 𝕃

----------------------------------------------------------------------
-- syntax
----------------------------------------------------------------------

infixr 6 _::_ _++_ 
infixr 5 _shorter_ _longer_ 

----------------------------------------------------------------------
-- operations
----------------------------------------------------------------------

[_] : ∀ {ℓ} {A : Set ℓ} → A → 𝕃 A
[ x ] = x :: []

is-empty : ∀{ℓ}{A : Set ℓ} → 𝕃 A → 𝔹
is-empty [] = tt
is-empty (_ :: _) = ff

tail : ∀ {ℓ} {A : Set ℓ} → 𝕃 A → 𝕃 A
tail [] = []
tail (x :: xs) = xs

head : ∀{ℓ}{A : Set ℓ} → (l : 𝕃 A) → .(is-empty l ≡ ff) → A
head [] ()
head (x :: xs) _ = x

head2 : ∀{ℓ}{A : Set ℓ} → (l : 𝕃 A) → maybe A
head2 [] = nothing
head2 (a :: _) = just a

last : ∀{ℓ}{A : Set ℓ} → (l : 𝕃 A) → is-empty l ≡ ff → A
last [] ()
last (x :: []) _ = x
last (x :: (y :: xs)) _ = last (y :: xs) refl

init : ∀{ℓ}{A : Set ℓ} → (l : 𝕃 A) → is-empty l ≡ ff → 𝕃 A
init [] ()
init (x :: []) _ = []
init (x :: (y :: xs)) _ = x :: init (y :: xs) refl

_++_ : ∀ {ℓ} {A : Set ℓ} → 𝕃 A → 𝕃 A → 𝕃 A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

concat : ∀{ℓ}{A : Set ℓ} → 𝕃 (𝕃 A) → 𝕃 A
concat [] = []
concat (l :: ls) = l ++ concat ls

repeat : ∀{ℓ}{A : Set ℓ} → ℕ → A → 𝕃 A
repeat 0 a = []
repeat (suc n) a = a :: (repeat n a)

map : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → B) → 𝕃 A → 𝕃 B
map f []        = []
map f (x :: xs) = f x :: map f xs

-- The hom part of the list functor.
list-funct : {A B : Set} → (A → B) → (𝕃 A → 𝕃 B)
list-funct f l = map f l

{- (maybe-map f xs) returns (just ys) if f returns (just y_i) for each
   x_i in the list xs.  Otherwise, (maybe-map f xs) returns nothing. -}
𝕃maybe-map : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → maybe B) → 𝕃 A → maybe (𝕃 B)
𝕃maybe-map f []       = just []
𝕃maybe-map f (x :: xs) with f x
𝕃maybe-map f (x :: xs) | nothing = nothing
𝕃maybe-map f (x :: xs) | just y with 𝕃maybe-map f xs
𝕃maybe-map f (x :: xs) | just y | nothing = nothing
𝕃maybe-map f (x :: xs) | just y | just ys = just (y :: ys)

foldr : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'} → (A → B → B) → B → 𝕃 A → B
foldr f b [] = b
foldr f b (a :: as) = f a (foldr f b as)

length : ∀{ℓ}{A : Set ℓ} → 𝕃 A → ℕ
length [] = 0
length (x :: xs) = suc (length xs)

reverse-helper : ∀ {ℓ}{A : Set ℓ} → 𝕃 A → 𝕃 A → 𝕃 A
reverse-helper h [] = h
reverse-helper h (x :: xs) = reverse-helper (x :: h) xs

reverse : ∀ {ℓ}{A : Set ℓ} → 𝕃 A → 𝕃 A
reverse l = reverse-helper [] l

nreverse : ∀{A : Set} → 𝕃 A → 𝕃 A
nreverse [] = []
nreverse (x :: xs) = nreverse xs ++ [ x ] 

list-member : ∀{ℓ}{A : Set ℓ}(eq : A → A → 𝔹)(a : A)(l : 𝕃 A) → 𝔹
list-member eq a [] = ff
list-member eq a (x :: xs) = eq a x || list-member eq a xs

list-in : ∀{A : Set}(a : A)(l : 𝕃 A) → Set
list-in a [] = ⊥
list-in a (b :: l) = a ≡ b ∨ list-in a l

unique : ∀{A : Set}(eq : A → A → 𝔹)(vs : 𝕃 A) → 𝔹
unique _ [] = tt
unique eq (x :: xs) = ~ list-member eq x xs && unique eq xs

-- like Data.List.find in Haskell
find : ∀{ℓ}{A : Set ℓ}(pred : A → 𝔹)(l : 𝕃 A) → maybe A
find pred [] = nothing
find pred (x :: xs) with pred x
find pred (x :: xs) | tt = just x
find pred (x :: xs) | ff = find pred xs

list-minus : ∀{ℓ}{A : Set ℓ}(eq : A → A → 𝔹)(l1 l2 : 𝕃 A) → 𝕃 A
list-minus eq [] l2 = []
list-minus eq (x :: xs) l2 = 
  let r = list-minus eq xs l2 in
    if list-member eq x l2 then r else x :: r

_longer_ : ∀{ℓ}{A : Set ℓ}(l1 l2 : 𝕃 A) → 𝔹
[] longer y = ff
(x :: xs) longer [] = tt
(x :: xs) longer (y :: ys) = xs longer ys

_shorter_ : ∀{ℓ}{A : Set ℓ}(l1 l2 : 𝕃 A) → 𝔹
x shorter y = y longer x

-- return tt iff all elements in the list satisfy the given predicate pred.
list-all : ∀{ℓ}{A : Set ℓ}(pred : A → 𝔹)(l : 𝕃 A) → 𝔹
list-all pred [] = tt
list-all pred (x :: xs) = pred x && list-all pred xs

all-pred : {X : Set} → (X → Set) → 𝕃 X → Set
all-pred f [] = ⊤
all-pred f (x₁ :: xs) = (f x₁) ∧ (all-pred f xs) 

-- return tt iff at least one element in the list satisfies the given predicate pred.
list-any : ∀{ℓ}{A : Set ℓ}(pred : A → 𝔹)(l : 𝕃 A) → 𝔹
list-any pred [] = ff
list-any pred (x :: xs) = pred x || list-any pred xs

list-and : (l : 𝕃 𝔹) → 𝔹
list-and [] = tt
list-and (x :: xs) = x && (list-and xs)

list-or : (l : 𝕃 𝔹) → 𝔹
list-or [] = ff
list-or (x :: l) = x || list-or l

list-max : ∀{ℓ}{A : Set ℓ} (lt : A → A → 𝔹) → 𝕃 A → A → A
list-max lt [] x = x
list-max lt (y :: ys) x = list-max lt ys (if lt y x then x else y)

isSublist : ∀{ℓ}{A : Set ℓ} → 𝕃 A → 𝕃 A → (A → A → 𝔹) → 𝔹
isSublist l1 l2 eq = list-all (λ a → list-member eq a l2) l1

-- set version, with equality predicate
sublist : ∀{A : Set} → 𝕃 A → 𝕃 A → Set
sublist{A} l1 l2 = ∀{x : A} → list-in x l1 → list-in x l2

disjoint : ∀{A : Set} → (A → A → 𝔹) → 𝕃 A → 𝕃 A → 𝔹
disjoint eq l1 l2 = list-all (λ x → ~ list-member eq x l2) l1

diagonal : ∀{A : Set} → 𝕃 A → 𝕃 (A × A)
diagonal = map (λ x → x , x) 

distinct : ∀{A : Set} → (A → A → 𝔹) → 𝕃 A → 𝔹
distinct eq [] = tt
distinct eq (x :: xs) = ~ list-member eq x xs && distinct eq xs

=𝕃 : ∀{ℓ}{A : Set ℓ} → (A → A → 𝔹) → (l1 : 𝕃 A) → (l2 : 𝕃 A) → 𝔹
=𝕃 eq (a :: as) (b :: bs) = eq a b && =𝕃 eq as bs
=𝕃 eq [] [] = tt
=𝕃 eq _ _ = ff

filter : ∀{ℓ}{A : Set ℓ} → (A → 𝔹) → 𝕃 A → 𝕃 A
filter p [] = []
filter p (x :: xs) = let r = filter p xs in 
                     if p x then x :: r else r

-- remove all elements equal to the given one
remove : ∀{ℓ}{A : Set ℓ}(eq : A → A → 𝔹)(a : A)(l : 𝕃 A) → 𝕃 A
remove eq a l = filter (λ x → ~ (eq a x)) l

{- nthTail n l returns the part of the list after the first n elements, 
   or [] if the list has fewer than n elements -}
nthTail : ∀{ℓ}{A : Set ℓ} → ℕ → 𝕃 A → 𝕃 A
nthTail 0 l = l
nthTail n [] = []
nthTail (suc n) (x :: l) = nthTail n l

splitAt : ∀{ℓ}{A : Set ℓ} → ℕ → 𝕃 A → (𝕃 A × 𝕃 A)
splitAt 0 xs = ([] , xs)
splitAt (suc n) [] = ([] , [])
splitAt (suc n) (x :: xs) with splitAt n xs
splitAt (suc n) (x :: xs) | (l , r) = (x :: l , r)

nth : ∀{ℓ}{A : Set ℓ} → ℕ → 𝕃 A → maybe A
nth _ [] = nothing
nth 0 (x :: xs) = just x
nth (suc n) (x :: xs) = nth n xs

-- nats-down N returns N :: (N-1) :: ... :: 0 :: []
nats-down : ℕ → 𝕃 ℕ
nats-down 0 = [ 0 ]
nats-down (suc x) = suc x :: nats-down x

zip : ∀{ℓ₁ ℓ₂}{A : Set ℓ₁}{B : Set ℓ₂} → 𝕃 A → 𝕃 B → 𝕃 (A × B)
zip [] [] = []
zip [] (x :: l₂) = []
zip (x :: l₁) [] = []
zip (x :: l₁) (y :: l₂) = (x , y) :: zip l₁ l₂

unzip : ∀{ℓ₁ ℓ₂}{A : Set ℓ₁}{B : Set ℓ₂} → 𝕃 (A × B) → (𝕃 A × 𝕃 B)
unzip [] = ([] , [])
unzip ((x , y) :: ps) with unzip ps
... | (xs , ys) = x :: xs , y :: ys

map-⊎ : {ℓ₁ ℓ₂ ℓ₃ : Level} → {A : Set ℓ₁}{B : Set ℓ₂}{C : Set ℓ₃} → (A → C) → (B → C) → 𝕃 (A ⊎ B) → 𝕃 C
map-⊎ f g [] = []
map-⊎ f g (inj₁ x :: l) = f x :: map-⊎ f g l
map-⊎ f g (inj₂ y :: l) = g y :: map-⊎ f g l

proj-⊎₁ : {ℓ ℓ' : Level}{A : Set ℓ}{B : Set ℓ'} → 𝕃 (A ⊎ B) → (𝕃 A)
proj-⊎₁ [] = []
proj-⊎₁ (inj₁ x :: l) = x :: proj-⊎₁ l
proj-⊎₁ (inj₂ y :: l) = proj-⊎₁ l

proj-⊎₂ : {ℓ ℓ' : Level}{A : Set ℓ}{B : Set ℓ'} → 𝕃 (A ⊎ B) → (𝕃 B)
proj-⊎₂ [] = []
proj-⊎₂ (inj₁ x :: l) = proj-⊎₂ l
proj-⊎₂ (inj₂ y :: l) = y :: proj-⊎₂ l

drop-nothing : ∀{ℓ}{A : Set ℓ} → 𝕃 (maybe A) → 𝕃 A
drop-nothing [] = []
drop-nothing (nothing :: aa) = drop-nothing aa
drop-nothing (just a :: aa) = a :: drop-nothing aa

null : ∀{ℓ}{A : Set ℓ} → 𝕃 A → 𝔹
null [] = tt
null (x :: xs) = ff

_>>=𝕃_ : ∀{A B : Set} → 𝕃 A → (A → 𝕃 B) → 𝕃 B
xs >>=𝕃 f = concat (map f xs)

_::₁_ : ∀{A B : Set} → A → 𝕃 A × 𝕃 B → 𝕃 A × 𝕃 B
_::₁_ a (xs , ys) = a :: xs , ys

_::₂_ : ∀{A B : Set} → B → 𝕃 A × 𝕃 B → 𝕃 A × 𝕃 B
_::₂_ b (xs , ys) = xs , b :: ys
