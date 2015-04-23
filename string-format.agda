{- formatted printing like printf, except type-safe (as proposed
   in "Cayenne -- a language with dependent types" by Augustsson).

   The types of the rest of the arguments are computed from the
   format string.  -}
module string-format where

open import char
open import eq
open import list
open import nat

open import nat-to-string
open import string

{- for partial evaluation of the type computed from the format
   string to make progress in tandem with the term for formatted
   printing, we need to use a view, as proposed in "The view 
   from the left" by McBride and McKinna. -}
data format-view : 𝕃 char → Set where
  format-nat : (s : 𝕃 char) → format-view ('%' :: 'n' :: s)
  format-string : (s : 𝕃 char) → format-view ('%' :: 's' :: s)
  not-format : (c : char)(s : 𝕃 char) → format-view (c :: s)
  empty-format : format-view []

format-cover : (s : 𝕃 char) → format-view s
format-cover ('%' :: 'n' :: s) = format-nat s
format-cover ('%' :: 's' :: s) = format-string s
format-cover (c :: s) = not-format c s
format-cover [] = empty-format

format-th : 𝕃 char → Set
format-th s with format-cover s
format-th .('%' :: 'n' :: f) | format-nat f = ℕ → format-th f
format-th .('%' :: 's' :: f) | format-string f = string → format-th f
format-th .(c :: f) | not-format c f = format-th f
format-th .[] | empty-format = string

format-t : string → Set
format-t s = format-th (string-to-𝕃char s)

format-h : 𝕃 char → (f : 𝕃 char) → format-th f
format-h s f with format-cover f
format-h s .('%' :: 'n' :: f) | format-nat f = λ n → format-h (s ++ (string-to-𝕃char (ℕ-to-string n))) f
format-h s .('%' :: 's' :: f) | format-string f = λ s' → format-h (s ++ (string-to-𝕃char s')) f
format-h s .(c :: f) | not-format c f = format-h (s ++ [ c ] ) f
format-h s .[] | empty-format = 𝕃char-to-string s

format : (s : string) → format-t s
format s = format-h [] (string-to-𝕃char s)

format-type-test : ℕ → string → string → string → string
format-type-test = format "%n% of the %ss are in the %s %s"

format-test1 : format "%n% of the %ss are in the %s" 25 "dog" "doghouse" ≡ "25% of the dogs are in the doghouse"
format-test1 = refl