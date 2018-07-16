-- pull in Haskell Ints
module int where

open import bool
open import string

postulate 
  int : Set
  int0 : int
  int1 : int
  _+int_ : int → int → int
  _*int_ : int → int → int
  _-int_ : int → int → int
  string-to-int : string → int
  is-zero-int : int → 𝔹

{-# COMPILE GHC int = type Int #-}
{-# COMPILE GHC int0 = 0 #-}
{-# COMPILE GHC int1 = 1 #-}
{-# COMPILE GHC _+int_ = (+) #-}
{-# COMPILE GHC _*int_ = (*) #-}
{-# COMPILE GHC _-int_ = (-) #-}
{-# COMPILE GHC string-to-int x = read x :: Int #-}
{-# COMPILE GHC is-zero-int = (==) 0 #-}
