module level where

import Agda.Primitive 

open Agda.Primitive public
  using    (Level ; _⊔_ ; lsuc ; lzero)

level = Level

lone : level
lone = lsuc lzero

