module trie-fast where

open import trie-core public
open import string
open import maybe
open import char
open import bool
open import eq

trie-lookup-fast3 : ∀{A : Set} → trie A → string → maybe A
trie-lookup-fast3{A} t s
  = extract (stringFoldl f t s)
  where
    extract : trie A → maybe A
    extract (trie.Node x _) = x

    -- define an "empty trie" and change this to:
    --  (trie A) → char → (trie A)
    f : trie A → char → trie A
    f (Node _ ts) c with cal-lookup ts c
    f (Node _ ts) c | nothing = Node nothing empty-cal
    f (Node _ ts) c | just t = t

trie-lookup : ∀{A : Set} → trie A → string → maybe A
trie-lookup = trie-lookup-fast3

trie-insert-fast2 : ∀{A : Set} → trie A → string → A → trie A
trie-insert-fast2{A} t s new-data = (stringFoldr g initial-f s) t
  where
   initial-f : trie A → trie A
   initial-f (Node _ ts) = Node (just new-data) ts

   g : char → (trie A → trie A) → (trie A → trie A)
   g c f (Node odata ts) with cal-lookup ts c
   g c f (Node odata ts) | nothing = Node odata (cal-add ts c (f empty-trie))
   g c f (Node odata ts) | just t = Node odata (cal-insert ts c (f t))


trie-insert : ∀{A : Set} → trie A → string → A → trie A
trie-insert = trie-insert-fast2

trie-remove-fast : ∀{A : Set} → trie A → string → trie A
trie-remove-fast{A} t s = (stringFoldr g initial-f s) t
  where
   initial-f : trie A → trie A
   initial-f (Node _ ts) = Node nothing ts

   g : char → (trie A → trie A) → (trie A → trie A)
   g c f (Node odata ts) with cal-lookup ts c
   g c f (Node odata ts) | nothing = Node odata ts
   g c f (Node odata ts) | just t = Node odata (cal-insert ts c (f t))

trie-remove : ∀{A : Set} → trie A → string → trie A
trie-remove = trie-remove-fast

open import trie-functions trie-lookup trie-insert trie-remove public
