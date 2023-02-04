module trie-core where

open import bool
open import char
open import list
open import maybe
open import product
open import string
open import unit
open import eq
open import nat

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

cal-remove : ∀ {A : Set} → cal A → char → cal A
cal-remove [] _ = []
cal-remove ((c , a) :: l) c' with c =char c'
... | tt = cal-remove l c'
... | ff = (c , a) :: cal-remove l c'

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

trie-insert-h : ∀{A : Set} → trie A → 𝕃 char → A → trie A
trie-insert-h (Node odata ts) [] x = (Node (just x) ts)
trie-insert-h (Node odata ts) (c :: cs) x with cal-lookup ts c
trie-insert-h (Node odata ts) (c :: cs) x | just t =
  (Node odata (cal-insert ts c (trie-insert-h t cs x)))
trie-insert-h (Node odata ts) (c :: cs) x | nothing =
  (Node odata (cal-add ts c (trie-insert-h empty-trie cs x)))

trie-remove-h : ∀{A : Set} → trie A → 𝕃 char → trie A
trie-remove-h (Node odata ts) (c :: cs) with cal-lookup ts c
trie-remove-h (Node odata ts) (c :: cs) | nothing = Node odata ts
trie-remove-h (Node odata ts) (c :: cs) | just t = Node odata (cal-insert ts c (trie-remove-h t cs))
trie-remove-h (Node odata ts) [] = Node nothing ts
