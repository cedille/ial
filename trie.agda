module trie where

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

trie-lookup-safe : ∀{A : Set} → trie A → string → maybe A
trie-lookup-safe t s = trie-lookup-h t (string-to-𝕃char s)

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
    extract (Node x _) = x

    -- define an "empty trie" and change this to:
    --  (trie A) → char → (trie A)
    f : trie A → char → trie A
    f (Node _ ts) c with cal-lookup ts c
    f (Node _ ts) c | nothing = Node nothing empty-cal
    f (Node _ ts) c | just t = t

trie-lookup : ∀{A : Set} → trie A → string → maybe A
-- trie-lookup = trie-lookup-safe
-- trie-lookup = trie-lookup-fast
-- trie-lookup = trie-lookup-fast2
trie-lookup = trie-lookup-fast3

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

trie-insert-safe : ∀{A : Set} → trie A → string → A → trie A
trie-insert-safe t s x = trie-insert-h t (string-to-𝕃char s) x


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
-- trie-insert = trie-insert-safe
trie-insert = trie-insert-fast2

trie-remove-h : ∀{A : Set} → trie A → 𝕃 char → trie A
trie-remove-h (Node odata ts) (c :: cs) with cal-lookup ts c
trie-remove-h (Node odata ts) (c :: cs) | nothing = Node odata ts
trie-remove-h (Node odata ts) (c :: cs) | just t = Node odata (cal-insert ts c (trie-remove-h t cs))
trie-remove-h (Node odata ts) [] = Node nothing ts

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
trie-remove-safe t s = trie-remove-h t (string-to-𝕃char s) 

trie-remove : ∀{A : Set} → trie A → string → trie A
-- trie-remove = trie-remove-safe
trie-remove = trie-remove-fast

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


bool-to-string : 𝔹 → string
bool-to-string tt = "true"
bool-to-string ff = "false"

insert-test1 : (trie-to-string ":" bool-to-string (trie-insert-safe empty-trie "hi" tt)) ≡ "hi:true\n"
insert-test1 = refl

-- insert-test2 : (trie-to-string ":" bool-to-string (trie-insert-fast empty-trie "hi" tt)) ≡ "hi:true\n"
-- insert-test2 = {!!}

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
