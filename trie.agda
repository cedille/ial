module trie where

open import string
open import maybe
open import trie-core public
open import empty

trie-lookup : ∀{A : Set} → trie A → string → maybe A
trie-lookup t s = trie-lookup-h t (string-to-𝕃char s)

trie-insert : ∀{A : Set} → trie A → string → A → trie A
trie-insert t s x = trie-insert-h t (string-to-𝕃char s) x

trie-remove : ∀{A : Set} → trie A → string → trie A
trie-remove t s = trie-remove-h t (string-to-𝕃char s)

open import trie-functions trie-lookup trie-insert trie-remove public
