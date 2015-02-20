module list where

open import bool
open import eq
open import maybe
open import nat


----------------------------------------------------------------------
-- datatypes
----------------------------------------------------------------------

data 𝕃 {ℓ} (A : Set ℓ) : Set ℓ where
  [] : 𝕃 A
  _::_ : (x : A) (xs : 𝕃 A) → 𝕃 A

{-# BUILTIN LIST 𝕃 #-}
{-# BUILTIN NIL  []   #-}
{-# BUILTIN CONS _::_  #-}

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

tail : ∀ {ℓ} {A : Set ℓ} → 𝕃 A → 𝕃 A
tail [] = []
tail (x :: xs) = xs

_++_ : ∀ {ℓ} {A : Set ℓ} → 𝕃 A → 𝕃 A → 𝕃 A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

repeat : ∀{ℓ}{A : Set ℓ} → ℕ → A → 𝕃 A
repeat 0 a = []
repeat (suc n) a = a :: (repeat n a)

map : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → B) → 𝕃 A → 𝕃 B
map f []        = []
map f (x :: xs) = f x :: map f xs

{- (maybe-map f xs) returns (just ys) if f returns (just y_i) for each
   x_i in the list xs.  Otherwise, (maybe-map f xs) returns nothing. -}
maybe-map : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → maybe B) → 𝕃 A → maybe (𝕃 B)
maybe-map f []       = just []
maybe-map f (x :: xs) with f x
maybe-map f (x :: xs) | nothing = nothing
maybe-map f (x :: xs) | just y with maybe-map f xs
maybe-map f (x :: xs) | just y | nothing = nothing
maybe-map f (x :: xs) | just y | just ys = just (y :: ys)

foldr : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'} → (A → B → B) → B → 𝕃 A → B
foldr f b [] = b
foldr f b (a :: as) = f a (foldr f b as)

length : ∀{ℓ}{A : Set ℓ} → 𝕃 A → ℕ
length [] = 0
length (x :: xs) = suc (length xs)

reverse-helper : ∀ {ℓ}{A : Set ℓ} → (𝕃 A) → (𝕃 A) → 𝕃 A
reverse-helper h [] = h
reverse-helper h (x :: xs) = reverse-helper (x :: h) xs

reverse : ∀ {ℓ}{A : Set ℓ} → 𝕃 A → 𝕃 A
reverse l = reverse-helper [] l

list-member : ∀{ℓ}{A : Set ℓ}(eq : A → A → 𝔹)(a : A)(l : 𝕃 A) → 𝔹
list-member eq a [] = ff
list-member eq a (x :: xs) with eq a x
... | tt = tt
... | ff = list-member eq a xs

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

-- return tt iff at least one element in the list satisfies the given predicate pred.
list-any : ∀{ℓ}{A : Set ℓ}(pred : A → 𝔹)(l : 𝕃 A) → 𝔹
list-any pred [] = ff
list-any pred (x :: xs) = pred x || list-any pred xs

list-and : (l : 𝕃 𝔹) → 𝔹
list-and [] = tt
list-and (x :: xs) = x && (list-and xs)

is-empty : ∀{ℓ}{A : Set ℓ} → 𝕃 A → 𝔹
is-empty [] = tt
is-empty (_ :: _) = ff

list-max : ∀{ℓ}{A : Set ℓ} (lt : A → A → 𝔹) → 𝕃 A → A → A
list-max lt [] x = x
list-max lt (y :: ys) x = list-max lt ys (if lt y x then x else y)

isSublist : ∀{ℓ}{A : Set ℓ} → 𝕃 A → 𝕃 A → (A → A → 𝔹) → 𝔹
isSublist l1 l2 eq = list-all (λ a → list-member eq a l2) l1

=𝕃 : ∀{ℓ}{A : Set ℓ} → (A → A → 𝔹) → (l1 : 𝕃 A) → (l2 : 𝕃 A) → 𝔹
=𝕃 eq (a :: as) (b :: bs) = eq a b && =𝕃 eq as bs
=𝕃 eq [] [] = tt
=𝕃 eq _ _ = ff

filter : ∀{ℓ}{A : Set ℓ} → (A → 𝔹) → 𝕃 A → 𝕃 A
filter p [] = []
filter p (x :: xs) = let r = filter p xs in 
                     if p x then x :: r else r

{- nthTail n l returns the part of the list after the first n elements, 
   or [] if the list has fewer than n elements -}
nthTail : ∀{ℓ}{A : Set ℓ} → ℕ → 𝕃 A → 𝕃 A
nthTail 0 l = l
nthTail n [] = []
nthTail (suc n) (x :: l) = nthTail n l