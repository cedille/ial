open import rel

module rtc  where

data _⋆ {A : Set} (r : Rel A) : Rel A where
  rtc-base : ∀{a a' : A} → r a a' → (r ⋆) a a'
  rtc-trans : ∀{a a' a'' : A} → (r ⋆) a a' → (r ⋆) a' a'' → (r ⋆) a a''