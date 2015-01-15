module trie-thms where

open import eq
open import list
open import maybe
open import string
open import trie

trie-lookup-empty-h : ∀ {A} x → trie-lookup-h{A} empty-trie x ≡ nothing
trie-lookup-empty-h [] = refl
trie-lookup-empty-h (_ :: _) = refl

trie-lookup-empty : ∀ {A} x → trie-lookup{A} empty-trie x ≡ nothing
trie-lookup-empty x = trie-lookup-empty-h (string-to-𝕃char x)

--trie-lookup-dec : ∀{A}{g : trie A}{x : A} → trie-lookup g x ≡ 