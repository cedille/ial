-- pull in Haskell Ints
module int where

open import bool
open import string
open import list
open import char
open import functions

postulate 
  int : Set
  int0 : int
  int1 : int
  _+int_ : int → int → int
  _*int_ : int → int → int
  _-int_ : int → int → int
  𝕃char-to-int : 𝕃 char → int
  is-zero-int : int → 𝔹

{-# COMPILE GHC int = type Int #-}
{-# COMPILE GHC int0 = 0 #-}
{-# COMPILE GHC int1 = 1 #-}
{-# COMPILE GHC _+int_ = (+) #-}
{-# COMPILE GHC _*int_ = (*) #-}
{-# COMPILE GHC _-int_ = (-) #-}
{-# COMPILE GHC 𝕃char-to-int = \ x -> read x :: Int #-}
{-# COMPILE GHC is-zero-int = (==) 0 #-}

string-to-int : string → int
string-to-int = 𝕃char-to-int ∘ string-to-𝕃char
