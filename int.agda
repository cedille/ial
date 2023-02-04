-- pull in Haskell Ints
module int where

open import bool
open import string
open import list
open import char
open import functions
open import nat

postulate
  int : Set
  int0 : int
  int1 : int
  _+int_ : int → int → int
  _*int_ : int → int → int
  _-int_ : int → int → int
  𝕃char-to-int : 𝕃 char → int
  int-to-𝕃char : int → 𝕃 char
  is-zero-int : int → 𝔹

{-# COMPILE GHC int = type Int #-}
{-# COMPILE GHC int0 = 0 #-}
{-# COMPILE GHC int1 = 1 #-}
{-# COMPILE GHC _+int_ = (+) #-}
{-# COMPILE GHC _*int_ = (*) #-}
{-# COMPILE GHC _-int_ = (-) #-}
{-# COMPILE GHC 𝕃char-to-int = \ x -> read x :: Int #-}
{-# COMPILE GHC int-to-𝕃char = \ x -> show x #-}
{-# COMPILE GHC is-zero-int = (==) 0 #-}

string-to-int : string → int
string-to-int = 𝕃char-to-int ∘ string-to-𝕃char

int-to-string : int → string
int-to-string = 𝕃char-to-string ∘ int-to-𝕃char

int-from-nat : ℕ → int
int-from-nat zero = int0
int-from-nat (suc n) = int1 +int (int-from-nat n)
