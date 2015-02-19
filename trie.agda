module trie where

open import bool
open import char
open import list
open import maybe
open import product
open import string
open import unit

cal : Set → Set
cal A = 𝕃 (char × A)

empty-cal : ∀{A : Set} → cal A
empty-cal = []

cal-lookup : ∀ {A : Set} → cal A → char → maybe A
cal-lookup [] _ = nothing
cal-lookup ((c , a) :: l) c' with c =char c'
... | tt = just a
... | ff = cal-lookup l c'

cal-insert : ∀ {A : Set} → cal A → char → A → cal A
cal-insert [] c a = (c , a) :: []
cal-insert ((c' , a') :: l) c a with c =char c'
... | tt = (c , a) :: l
... | ff = (c' , a') :: (cal-insert l c a)

cal-add : ∀{A : Set} → cal A → char → A → cal A
cal-add l c a = (c , a) :: l

test-cal-insert = cal-insert (('a' , 1) :: ('b' , 2) :: []) 'b' 20

data trie (A : Set) : Set where
  Node : maybe A → cal (trie A) → trie A

empty-trie : ∀{A : Set} → trie A
empty-trie = (Node nothing empty-cal)

trie-lookup-h : ∀{A : Set} → trie A → 𝕃 char → maybe A
trie-lookup-h (Node odata ts) (c :: cs) with cal-lookup ts c
trie-lookup-h (Node odata ts) (c :: cs) | nothing = nothing
trie-lookup-h (Node odata ts) (c :: cs) | just t = trie-lookup-h t cs
trie-lookup-h (Node odata ts) [] = odata

trie-lookup : ∀{A : Set} → trie A → string → maybe A
trie-lookup t s = trie-lookup-h t (string-to-𝕃char s)

trie-contains : ∀{A : Set} → trie A → string → 𝔹
trie-contains t s with trie-lookup t s
trie-contains t s | nothing = ff
trie-contains t s | just _ = tt

trie-insert-h : ∀{A : Set} → trie A → 𝕃 char → A → trie A
trie-insert-h (Node odata ts) [] x = (Node (just x) ts)
trie-insert-h (Node odata ts) (c :: cs) x with cal-lookup ts c
trie-insert-h (Node odata ts) (c :: cs) x | just t = 
  (Node odata (cal-insert ts c (trie-insert-h t cs x)))
trie-insert-h (Node odata ts) (c :: cs) x | nothing = 
  (Node odata (cal-add ts c (trie-insert-h empty-trie cs x)))

trie-insert : ∀{A : Set} → trie A → string → A → trie A
trie-insert t s x = trie-insert-h t (string-to-𝕃char s) x

trie-to-string-h : ∀{A : Set} → string → (A → string) → trie A → 𝕃 char → string
cal-trie-to-string-h : ∀{A : Set} → string → (A → string) → cal (trie A) → 𝕃 char → string
trie-to-string-h sep d (Node (just x) c) prev-str = 
  (𝕃char-to-string (reverse prev-str)) ^ sep ^ (d x) ^ "\n" ^ (cal-trie-to-string-h sep d c prev-str)
trie-to-string-h sep d (Node nothing c) prev-str = cal-trie-to-string-h sep d c prev-str
cal-trie-to-string-h sep d [] prev-str = ""
cal-trie-to-string-h sep d ((c , t) :: cs) prev-str = 
  (trie-to-string-h sep d t (c :: prev-str)) ^ (cal-trie-to-string-h sep d cs prev-str)

{- trie-to-string sep d t returns a string representation of the trie t, 
   where each mapping from string s to data x is printed as
     s sep d x
   where sep is a string and d returns a string for any element A of the trie. -}
trie-to-string : ∀{A : Set} → string → (A → string) → trie A → string
trie-to-string sep d t = trie-to-string-h sep d t []

trie-mappings-h : ∀{A : Set} → trie A → 𝕃 char → 𝕃 (string × A)
cal-trie-mappings-h : ∀{A : Set} → cal (trie A) → 𝕃 char → 𝕃 (string × A)
trie-mappings-h (Node (just x) c) prev-str = (𝕃char-to-string (reverse prev-str) , x) :: (cal-trie-mappings-h c prev-str)
trie-mappings-h (Node nothing c) prev-str = (cal-trie-mappings-h c prev-str)
cal-trie-mappings-h [] prev-str = []
cal-trie-mappings-h ((c , t) :: cs) prev-str = trie-mappings-h t (c :: prev-str) ++ (cal-trie-mappings-h cs prev-str)

trie-mappings : ∀{A : Set} → trie A → 𝕃 (string × A)
trie-mappings t = trie-mappings-h t []

----------------------------------------------------------------------
-- stringset
----------------------------------------------------------------------

stringset : Set
stringset = trie ⊤

stringset-contains : stringset → string → 𝔹
stringset-contains ss s = trie-contains ss s

stringset-insert : stringset → string → stringset
stringset-insert ss s = trie-insert ss s triv

empty-stringset : stringset
empty-stringset = empty-trie