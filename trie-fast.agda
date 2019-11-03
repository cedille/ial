module trie-fast where

open import trie hiding (trie-lookup ; trie-insert ; trie-remove) public
open import string
open import maybe
open import char
open import bool
open import eq

trie-lookup-safe : ∀{A : Set} → trie A → string → maybe A
trie-lookup-safe = trie.trie-lookup

-- trie-lookup-fast : ∀{A : Set} → trie A → string → maybe A
-- {-# TERMINATING #-}
-- trie-lookup-fast (Node odata ts) s with string-uncons s
-- trie-lookup-fast (Node odata ts) s | nothing = odata
-- trie-lookup-fast (Node odata ts) s | just (c , cs) with cal-lookup ts c
-- trie-lookup-fast (Node odata ts) s | just (c , cs) | nothing = nothing
-- trie-lookup-fast (Node odata ts) s | just (c , cs) | just t = trie-lookup-fast t cs

-- trie-lookup-fast2 : ∀{A : Set} → trie A → string → maybe A
-- trie-lookup-fast2{A} t s
--   = extract (stringFoldl f (just t) s)
--   where
--     extract : maybe (trie A) → maybe A
--     extract nothing = nothing
--     extract (just (Node odata _)) = odata

--     f : maybe (trie A) → char → maybe (trie A)
--     f nothing c = nothing
--     f (just (Node _ ts)) = cal-lookup ts

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

trie-insert-safe : ∀{A : Set} → trie A → string → A → trie A
trie-insert-safe = trie.trie-insert

trie-insert-fast2 : ∀{A : Set} → trie A → string → A → trie A
trie-insert-fast2{A} t s new-data = (stringFoldr g initial-f s) t
  where
   initial-f : trie A → trie A
   initial-f (Node _ ts) = Node (just new-data) ts

   g : char → (trie A → trie A) → (trie A → trie A)
   g c f (Node odata ts) with cal-lookup ts c
   g c f (Node odata ts) | nothing = Node odata (cal-add ts c (f empty-trie))
   g c f (Node odata ts) | just t = Node odata (cal-insert ts c (f t))

-- trie-insert-fast : ∀{A : Set} → trie A → string → A → trie A
-- trie-insert-fast{A} t s new-data = post-process (stringFoldl g (t , []) s)
--   where
--    foldl : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'} → (A → B → B) → B → 𝕃 A → B
--    foldl f b [] = b
--    foldl f b (x :: l) = foldl f (f x b) l

--    initial-f : trie A → trie A
--    initial-f (Node _ ts) = Node (just new-data) ts

--    post-process-f : (trie A → trie A) → (trie A) → trie A
--    post-process-f f t = f t

--    post-process : (trie A) × 𝕃 (trie A → trie A) → trie A
--    post-process (t , l) = foldl post-process-f (initial-f t) l

--    -- post-process (Node _ ts , []) = Node (just new-data) ts
--    -- post-process (t , f :: l) = post-process ({! !} , l)

--    nothing-case : maybe A → cal (trie A) → char → trie A → trie A
--    nothing-case odata ts c child = Node odata (cal-add ts c child)

--    just-case : maybe A → cal (trie A) → char → trie A → trie A
--    just-case odata ts c child = Node odata (cal-insert ts c child)
--    -- (Node odata (cal-insert ts c (trie-insert-h t cs x)))

--    g : (trie A) × 𝕃 (trie A → trie A) → char → (trie A) × 𝕃 (trie A → trie A)
--    g (Node odata ts , l) c with cal-lookup ts c 
--    g (Node odata ts , l) c | nothing = empty-trie , (nothing-case odata ts c :: l)
--    g (Node odata ts , l) c | just t = t , (just-case odata ts c) :: l

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

trie-remove-safe : ∀{A : Set} → trie A → string → trie A
trie-remove-safe = trie.trie-remove

trie-remove : ∀{A : Set} → trie A → string → trie A
trie-remove = trie-remove-fast

-- bool-to-string : 𝔹 → string
-- bool-to-string tt = "true"
-- bool-to-string ff = "false"

-- insert-test1 : (trie-to-string ":" bool-to-string (trie-insert-safe empty-trie "hi" tt)) ≡ "hi:true\n"
-- insert-test1 = refl

-- insert-test2 : (trie-to-string ":" bool-to-string (trie-insert-fast empty-trie "hi" tt)) ≡ "hi:true\n"
-- insert-test2 = {!!}

