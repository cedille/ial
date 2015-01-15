module io where

open import list
open import string
open import unit

----------------------------------------------------------------------
-- datatypes
----------------------------------------------------------------------

postulate
  IO : Set → Set

{-# COMPILED_TYPE IO IO #-}
{-# BUILTIN IO IO #-}

----------------------------------------------------------------------
-- syntax
----------------------------------------------------------------------

infixl 1 _>>=_
infixl 1 _>>_

----------------------------------------------------------------------
-- postulated operations
----------------------------------------------------------------------

postulate
  return : ∀ {A : Set} → A → IO A
  _>>=_  : ∀ {A B : Set} → IO A → (A → IO B) → IO B

{-# COMPILED return (\ _ -> return )   #-}
{-# COMPILED _>>=_  (\ _ _ -> (>>=)) #-}

postulate
  putStr : string -> IO ⊤

  -- Reads a file, which is assumed to be finite. 
  readFiniteFile : string → IO string

  writeFile : string → string → IO ⊤

private
  data simple-list (A : Set) : Set where
    nil : simple-list A
    cons : A → simple-list A → simple-list A
  
  simple-list-to-𝕃 : ∀ {A : Set} → simple-list A → 𝕃 A
  simple-list-to-𝕃 nil = []
  simple-list-to-𝕃 (cons x xs) = x :: (simple-list-to-𝕃 xs)

{-# COMPILED_DATA simple-list ([]) [] (:) #-}

private
  postulate
    privGetArgs : IO (simple-list string)

{-# COMPILED putStr         putStr                #-}
{-# COMPILED readFiniteFile readFile #-}
{-# COMPILED writeFile      writeFile             #-}
{-# IMPORT System.Environment #-}
{-# COMPILED privGetArgs System.Environment.getArgs #-}

getArgs : IO (𝕃 string)
getArgs = privGetArgs >>= (λ args → return (simple-list-to-𝕃 args))

----------------------------------------------------------------------
-- defined operations
----------------------------------------------------------------------

_>>_ : ∀ {A B : Set} → IO A → IO B → IO B
x >> y = x >>= (λ q -> y)