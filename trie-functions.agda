open import trie-core
open import string
open import maybe

module trie-functions (trie-lookup : ∀{A : Set} → trie A → string → maybe A)
                      (trie-insert : ∀{A : Set} → trie A → string → A → trie A)
                      (trie-remove : ∀{A : Set} → trie A → string → trie A) where

open import bool
open import char
open import list
open import product
open import unit
open import eq
open import nat

trie-contains : ∀{A : Set} → trie A → string → 𝔹
trie-contains t s with trie-lookup t s
trie-contains t s | nothing = ff
trie-contains t s | just _ = tt

trie-map : ∀{A B : Set} → (A → B) → trie A → trie B
trie-cal-map : ∀{A B : Set} → (A → B) → cal (trie A) → cal (trie B)
trie-map f (Node x x₁) = Node (maybe-map f x) (trie-cal-map f x₁)
trie-cal-map f [] = []
trie-cal-map f ((c , t) :: cs) =
  (c , trie-map f t) :: trie-cal-map f cs

trie-to-string-h : ∀{A : Set} → string → (A → string) → trie A → 𝕃 char → string
trie-cal-to-string-h : ∀{A : Set} → string → (A → string) → cal (trie A) → 𝕃 char → string
trie-to-string-h sep d (Node (just x) c) prev-str =
  (𝕃char-to-string (reverse prev-str)) ^ sep ^ (d x) ^ "\n" ^ (trie-cal-to-string-h sep d c prev-str)
trie-to-string-h sep d (Node nothing c) prev-str = trie-cal-to-string-h sep d c prev-str
trie-cal-to-string-h sep d [] prev-str = ""
trie-cal-to-string-h sep d ((c , t) :: cs) prev-str =
  (trie-to-string-h sep d t (c :: prev-str)) ^ (trie-cal-to-string-h sep d cs prev-str)

{- trie-to-string sep d t returns a string representation of the trie t,
   where each mapping from string s to data x is printed as
     s sep d x
   where sep is a string and d returns a string for any element A of the trie. -}
trie-to-string : ∀{A : Set} → string → (A → string) → trie A → string
trie-to-string sep d t = trie-to-string-h sep d t []

trie-mappings-h : ∀{A : Set} → trie A → 𝕃 char → 𝕃 (string × A)
trie-cal-mappings-h : ∀{A : Set} → cal (trie A) → 𝕃 char → 𝕃 (string × A)
trie-mappings-h (Node (just x) c) prev-str = (𝕃char-to-string (reverse prev-str) , x) :: (trie-cal-mappings-h c prev-str)
trie-mappings-h (Node nothing c) prev-str = (trie-cal-mappings-h c prev-str)
trie-cal-mappings-h [] prev-str = []
trie-cal-mappings-h ((c , t) :: cs) prev-str = trie-mappings-h t (c :: prev-str) ++ (trie-cal-mappings-h cs prev-str)

trie-mappings : ∀{A : Set} → trie A → 𝕃 (string × A)
trie-mappings t = trie-mappings-h t []

-- return a list of all the strings which have associated data in the trie
trie-strings : ∀{A : Set} → trie A → 𝕃 string
trie-strings t = map fst (trie-mappings t)

trie-size : ∀{A : Set} → trie A → ℕ
trie-size t = length (trie-strings t)

trie-nonempty : ∀{A : Set} → trie A → 𝔹
trie-cal-nonempty : ∀{A : Set} → cal (trie A) → 𝔹
trie-nonempty (Node (just x) t) = tt
trie-nonempty (Node nothing c) = trie-cal-nonempty c
trie-cal-nonempty [] = ff
trie-cal-nonempty ((a , t) :: c) = trie-nonempty t || trie-cal-nonempty c

----------------------------------------------------------------------
-- list-tries, which map strings to lists of values
----------------------------------------------------------------------

𝕃trie : Set → Set
𝕃trie A = trie (𝕃 A)

𝕃trie-lookup : ∀{A : Set} → 𝕃trie A → string → 𝕃 A
𝕃trie-lookup t s with trie-lookup t s
... | nothing = []
... | just l = l

𝕃trie-add : ∀{A : Set} → trie (𝕃 A) → string → A → trie (𝕃 A)
𝕃trie-add t s a = trie-insert t s (a :: 𝕃trie-lookup t s)

𝕃trie-add* : ∀{A : Set} → trie (𝕃 A) → string → 𝕃 A → trie (𝕃 A)
𝕃trie-add* t s aa = trie-insert t s (aa ++ 𝕃trie-lookup t s)

----------------------------------------------------------------------
-- stringset
----------------------------------------------------------------------

stringset : Set
stringset = trie ⊤

stringset-contains : stringset → string → 𝔹
stringset-contains ss s = trie-contains ss s

stringset-insert : stringset → string → stringset
stringset-insert ss s = trie-insert ss s triv

stringset-remove : stringset → string → stringset
stringset-remove ss s = trie-remove ss s

stringset-insert𝕃 : stringset → 𝕃 char → stringset
stringset-insert𝕃 ss s = trie-insert-h ss s triv

empty-stringset : stringset
empty-stringset = empty-trie

stringset-insert* : stringset → 𝕃 string → stringset
stringset-insert* s [] = s
stringset-insert* s (x :: xs) = stringset-insert (stringset-insert* s xs) x

stringset-strings : ∀{A : Set} → trie A → 𝕃 string
stringset-strings t = map fst (trie-mappings t)
