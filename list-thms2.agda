module list-thms2 where

open import bool
open import bool-thms
open import bool-thms2
open import functions
open import list
open import list-thms
open import nat
open import nat-thms
open import product-thms
open import logic
open import bool-relations as B

list-and-++ : ∀(l1 l2 : 𝕃 𝔹) → list-and (l1 ++ l2) ≡ (list-and l1) && (list-and l2)
list-and-++ [] l2 = refl
list-and-++ (x :: l1) l2 rewrite (list-and-++ l1 l2) | (&&-assoc x (list-and l1) (list-and l2))= refl

list-or-++ : ∀(l1 l2 : 𝕃 𝔹) → list-or (l1 ++ l2) ≡ (list-or l1) || (list-or l2)
list-or-++ [] l2 = refl
list-or-++ (x :: l1) l2 rewrite (list-or-++ l1 l2) | (||-assoc x (list-or l1) (list-or l2))  = refl

++-singleton : ∀{ℓ}{A : Set ℓ}(a : A)(l1 l2 : 𝕃 A) → (l1 ++ [ a ]) ++ l2 ≡ l1 ++ (a :: l2)
++-singleton a l1 [] rewrite ++[] (l1 ++ a :: []) = refl
++-singleton a l1 l2  rewrite (++-assoc l1 [ a ] l2) = refl

list-member-++ : ∀{ℓ}{A : Set ℓ}(eq : A → A → 𝔹)(a : A)(l1 l2 : 𝕃 A) → 
                 list-member eq a (l1 ++ l2) ≡ (list-member eq a l1) || (list-member eq a l2)
list-member-++ eq a [] l2 = refl
list-member-++ eq a (x :: l1) l2 with eq a x
list-member-++ eq a (x :: l1) l2 | tt = refl
list-member-++ eq a (x :: l1) l2 | ff rewrite (list-member-++ eq a l1 l2) = refl

list-member-++2 : ∀{ℓ}{A : Set ℓ}(eq : A → A → 𝔹)(a : A)(l1 l2 : 𝕃 A) → 
                   list-member eq a l1 ≡ tt → 
                   list-member eq a (l1 ++ l2) ≡ tt
list-member-++2 eq a [] l2 ()
list-member-++2 eq a (x :: l1) l2 p with eq a x
list-member-++2 eq a (x :: l1) l2 p | tt = refl
list-member-++2 eq a (x :: l1) l2 p | ff rewrite (list-member-++2 eq a l1 l2 p) = refl


list-member-++3 : ∀{ℓ}{A : Set ℓ}(eq : A → A → 𝔹)(a : A)(l1 l2 : 𝕃 A) →  
                   list-member eq a l2 ≡ tt → 
                   list-member eq a (l1 ++ l2) ≡ tt
list-member-++3 eq a [] l2 p = p
list-member-++3 eq a (x :: l1) l2 p with eq a x
list-member-++3 eq a (x :: l1) l2 p | tt = refl
list-member-++3 eq a (x :: l1) l2 p | ff rewrite (list-member-++3 eq a l1 l2 p) = refl

filter-ff-repeat : ∀{ℓ}{A : Set ℓ}{p : A → 𝔹}{a : A}(n : ℕ) →
                     p a ≡ ff → 
                     filter p (repeat n a) ≡ []
filter-ff-repeat zero p1 = refl
filter-ff-repeat{ℓ}{A}{p0}{a} (suc n) p1 with keep (p0 a)
filter-ff-repeat{ℓ}{A}{p0}{a} (suc n) p1 | tt , y rewrite y = 𝔹-contra (sym p1)
filter-ff-repeat{ℓ}{A}{p0}{a} (suc n) p1 | ff , y rewrite y = filter-ff-repeat {ℓ} {A} {p0} {a} n y

is-empty-distr : ∀{ℓ}{A : Set ℓ} (l1 l2 : 𝕃 A) → is-empty (l1 ++ l2) ≡ (is-empty l1) && (is-empty l2)
is-empty-distr [] l2 = refl
is-empty-distr (x :: l1) l2 = refl

is-empty-reverse : ∀{ℓ}{A : Set ℓ}(l : 𝕃 A) → is-empty l ≡ is-empty (reverse l)
is-empty-reverse [] = refl
is-empty-reverse (x :: xs) rewrite (reverse-++h (x :: []) xs) | (is-empty-distr (reverse-helper [] xs) (x :: []))
                                 | (&&-comm (is-empty (reverse-helper [] xs)) ff) = refl

reverse-length : ∀{ℓ}{A : Set ℓ}(l : 𝕃 A) → length (reverse l) ≡ length l
reverse-length l = length-reverse-helper [] l

last-distr : ∀{ℓ}{A : Set ℓ}(l : 𝕃 A)(x : A)(p : is-empty l ≡ ff) → last (x :: l) refl ≡ last l p
last-distr [] x ()
last-distr (x :: l) x2 refl = refl

is-empty-[] : ∀{ℓ}{A : Set ℓ} (l : 𝕃 A)(p : is-empty l ≡ tt) → l ≡ []
is-empty-[] [] p = refl
is-empty-[] (x :: l) ()

rev-help-empty : ∀ {ℓ}{A : Set ℓ} (l1 l2 : 𝕃 A) → (p1 : is-empty l2 ≡ ff) → 
                      is-empty (reverse-helper l1 l2) ≡ ff
rev-help-empty l1 [] ()
rev-help-empty l1 (x :: l2) refl rewrite reverse-++h (x :: l1) l2 | is-empty-distr (reverse-helper [] l2) (x :: l1)
                                    | (&&-comm (is-empty (reverse-helper [] l2)) ff) = refl

is-empty-revh : ∀{ℓ}{A : Set ℓ}(h l : 𝕃 A) → is-empty l ≡ ff → is-empty (reverse-helper h l) ≡ ff
is-empty-revh h l p = rev-help-empty h l p

head-last-reverse-lem : ∀{ℓ}{A : Set ℓ}(h l : 𝕃 A)(p : is-empty l ≡ ff) → last l p ≡ head (reverse-helper h l) (is-empty-revh h l p)
head-last-reverse-lem h [] ()
head-last-reverse-lem h (x :: []) _ = refl
head-last-reverse-lem h (x :: y :: l) refl = head-last-reverse-lem (x :: h) (y :: l) refl

head-last-reverse : ∀{ℓ}{A : Set ℓ}(l : 𝕃 A)(p : is-empty l ≡ ff) → last l p ≡ head (reverse l) (rev-help-empty [] l p)
head-last-reverse [] ()
head-last-reverse (x :: l) p with keep (is-empty l)
head-last-reverse (x :: l) refl | tt , b rewrite is-empty-[] l b = refl
head-last-reverse (x :: l) refl | ff , b rewrite (last-distr l x b)  = head-last-reverse-lem (x :: []) l b

reverse-reverse : ∀{ℓ}{A : Set ℓ}(l : 𝕃 A) → reverse (reverse l) ≡ l
reverse-reverse [] = refl
reverse-reverse (x :: l) rewrite (reverse-++h (x :: []) l) | (reverse-++ (reverse-helper [] l) (x  :: [])) | reverse-reverse l = refl

empty++elem : ∀ {ℓ}{A : Set ℓ} (a : A) (l : 𝕃 A) → is-empty ( l ++ [ a ]) ≡ ff
empty++elem a [] = refl
empty++elem a (x :: l) = refl

last-++ : ∀{ℓ}{A : Set ℓ} (a : A) (l : 𝕃 A) → last (l ++ [ a ]) (empty++elem a l) ≡ a
last-++ a [] = refl
last-++ a (x :: l) rewrite last-distr (l ++ [ a ]) x (empty++elem a l) | last-++ a l = refl

disjoint-[] : ∀{A : Set}{l : 𝕃 A}{eq : A → A → 𝔹} →
               disjoint eq l [] ≡ tt
disjoint-[] {l = []} = refl
disjoint-[] {l = x :: l}{eq} = disjoint-[]{l = l}{eq}

disjoint-++ : ∀{A : Set}{l1 l2a l2b : 𝕃 A}{eq : A → A → 𝔹} →
               disjoint eq l1 (l2a ++ l2b) ≡ tt →
               disjoint eq l1 l2a ≡ tt ∧ disjoint eq l1 l2b ≡ tt
disjoint-++{A} {[]} {l2} {l2b}{eq} p = refl , refl
disjoint-++{A} {x :: l1} {l2a} {l2b}{eq} p with &&-elim{~ list-member eq x (l2a ++ l2b)} p
disjoint-++{A} {x :: l1} {l2a} {l2b}{eq} _ | p1 , p2 rewrite list-member-++{A = A} eq x l2a l2b |
 ~-over-|| (list-member eq x l2a) (list-member eq x l2b) with &&-elim{~ list-member eq x l2a} p1
disjoint-++{A} {x :: l1} {l2a} {l2b}{eq} _ | p1 , p2 | r1 , r2 rewrite r1 | r2 =
  disjoint-++{l1 = l1}{l2a}{l2b}{eq = eq} p2

disjoint-++i : ∀{A : Set}{l1 l2a l2b : 𝕃 A}{eq : A → A → 𝔹} →
                disjoint eq l1 l2a ≡ tt →
                disjoint eq l1 l2b ≡ tt → 
                disjoint eq l1 (l2a ++ l2b) ≡ tt 
disjoint-++i {l1 = []} {l2a} {l2b} {eq} u1 u2 = refl
disjoint-++i {l1 = x :: l1} {l2a} {l2b} {eq} u1 u2 with &&-elim{~ list-member eq x l2a} u1 | &&-elim{~ list-member eq x l2b} u2
disjoint-++i {l1 = x :: l1} {l2a} {l2b} {eq} u1 u2 | v1 , v2 | w1 , w2
  rewrite list-member-++ eq x l2a l2b | ~-≡-tt{list-member eq x l2a} v1 | ~-≡-tt{list-member eq x l2b} w1 =
  disjoint-++i{l1 = l1}{l2a}{l2b} v2 w2

disjoint-++2 : ∀{A : Set}{l1a l1b l2 : 𝕃 A}{eq : A → A → 𝔹} →
               disjoint eq (l1a ++ l1b) l2 ≡ tt →
               disjoint eq l1a l2 ≡ tt ∧ disjoint eq l1b l2 ≡ tt
disjoint-++2 {l1a = []} {l1b} {l2} {eq} u = refl , u
disjoint-++2 {l1a = x :: l1a} {l1b} {l2} {eq} u with &&-elim{~ list-member eq x l2} u
disjoint-++2 {l1a = x :: l1a} {l1b} {l2} {eq} u | u1 , u2 rewrite u1 = disjoint-++2{l1a = l1a}{l1b}{l2}{eq} u2

disjoint-++2i : ∀{A : Set}{l1a l1b l2 : 𝕃 A}{eq : A → A → 𝔹} →
                 disjoint eq l1a l2 ≡ tt → 
                 disjoint eq l1b l2 ≡ tt → 
                 disjoint eq (l1a ++ l1b) l2 ≡ tt 
disjoint-++2i{l1a = []}{l1b}{l2}{eq} u1 u2 = u2
disjoint-++2i{l1a = x :: l1a}{l1b}{l2}{eq} u1 u2 with &&-elim{~ list-member eq x l2} u1
disjoint-++2i{l1a = x :: l1a}{l1b}{l2}{eq} u1 u2 | v1 , v2 rewrite v1 = disjoint-++2i{l1a = l1a}{l1b}{l2}{eq} u1 u2

list-member-disjoint : ∀{A : Set}{x : A}{l : 𝕃 A}{eq : A → A → 𝔹} → 
                       ~ list-member eq x l ≡ tt →
                       B.symmetric eq → 
                       disjoint eq l [ x ] ≡ tt
list-member-disjoint {l = []} sm p = refl
list-member-disjoint {x = x}{l = y :: l}{eq} p sm with keep (eq x y)
list-member-disjoint {x = x}{l = y :: l}{eq} p sm | tt , q rewrite q | sm q with p 
list-member-disjoint {x = x}{l = y :: l}{eq} p sm | tt , q | () 
list-member-disjoint {x = x}{l = y :: l}{eq} p sm | ff , q rewrite q | ~symmetric eq sm q = 
  list-member-disjoint{x = x}{l = l} p sm 

disjoint-sym : ∀{A : Set}{l1 l2 : 𝕃 A}{eq : A → A → 𝔹} →
               B.symmetric eq → 
               disjoint eq l1 l2 ≡ tt →
               disjoint eq l2 l1 ≡ tt
disjoint-sym {l1 = []}{l2}{eq} sm u rewrite disjoint-[]{l = l2}{eq} = refl
disjoint-sym {l1 = x :: l1}{l2}{eq} sm u with disjoint-++2{l1a = [ x ]}{l1b = l1}{l2 = l2}{eq = eq} u
disjoint-sym {l1 = x :: l1}{l2}{eq} sm u | u1 , u2 rewrite &&-tt (~ list-member eq x l2) = 
  disjoint-++i{l1 = l2}{l2a = [ x ]}{l2b = l1} 
    (list-member-disjoint{x = x}{l = l2}{eq} u1 sm)
    (disjoint-sym{l1 = l1}{l2 = l2}{eq} sm u2)

all-pred-implies : ∀{X : Set}{f g : X → Set}{l : 𝕃 X} →
                   (∀{x} → f x → g x) → 
                   all-pred f l →
                   all-pred g l
all-pred-implies {l = []} p _ = triv
all-pred-implies {l = x :: l} p (u , u') = p u , all-pred-implies p u'

disjoint-in-out : ∀{A : Set}{l1 l2 : 𝕃 A}{x y : A}{eq : A → A → 𝔹} →
                  computational-equality eq → 
                  disjoint eq l1 l2 ≡ tt →
                  list-member eq x l1 ≡ tt →
                  list-member eq y l2 ≡ tt →
                  eq x y ≡ ff
disjoint-in-out {A} {x' :: l1} {l2} {x} {y} {eq} e dis xin yin with ||-elim{eq x x'} xin
disjoint-in-out {A} {x' :: l1} {y' :: l2} {x} {y} {eq} e dis xin yin | inj₁ q with ||-elim{eq y y'} yin 
disjoint-in-out {A} {x' :: l1} {y' :: l2} {x} {y} {eq} e dis xin yin | inj₁ q | inj₁ q' rewrite e q | e q' =
  ~-≡-tt (~||-elim1{eq x' y'} (&&-elim1 dis))
disjoint-in-out {A} {x' :: l1} {y' :: l2} {x} {y} {eq} e dis xin yin | inj₁ q | inj₂ rec =
  disjoint-in-out{A}{x' :: l1}{l2}{x}{y}{eq} e zz xin rec
  where zz : disjoint eq (x' :: l1) l2 ≡ tt
        zz = &&-intro (~||-elim2{eq x' y'} (&&-elim1 dis))
                      (list-all-sub l1 (λ a u → ~||-elim2{eq a y'} u) (&&-elim2 dis))
disjoint-in-out {A} {x' :: l1} {l2} {x} {y} {eq} e dis xin yin | inj₂ rec =
  disjoint-in-out {A} {l1} {l2} {x} {y} {eq} e (&&-elim2{~ list-member eq x' l2} dis) rec yin


member-in-out : ∀{A : Set}{l : 𝕃 A}{x y : A}{eq : A → A → 𝔹} →
                 computational-equality eq → 
                 list-member eq x l ≡ tt →
                 list-member eq y l ≡ ff →
                 eq x y ≡ ff
member-in-out {A} {z :: l} {x} {y} {eq} e inx outy with ||-elim{eq x z} inx 
member-in-out {A} {z :: l} {x} {y} {eq} e inx outy | inj₁ p rewrite e p with keep (eq z y)
member-in-out {A} {z :: l} {x} {y} {eq} e inx outy | inj₁ p | tt , q rewrite e q = sym (sym (||≡ff₁{eq y y} outy))
member-in-out {A} {z :: l} {x} {y} {eq} e inx outy | inj₁ p | ff , q = q
member-in-out {A} {z :: l} {x} {y} {eq} e inx outy | inj₂ p = member-in-out{A}{l}{x}{y}{eq} e p (||≡ff₂{eq y z} outy)

sublist-in-out : ∀{A : Set}{l1 l2 : 𝕃 A}{x y : A}{eq : A → A → 𝔹} →
                  computational-equality eq → 
                  isSublist l1 l2 eq ≡ tt →
                  list-member eq x l1 ≡ tt →
                  list-member eq y l2 ≡ ff →
                  eq x y ≡ ff
sublist-in-out{A}{l1}{l2}{x}{y}{eq} e sl m = member-in-out{A}{l2} e (list-member-sub{A}{eq}{x}{l1}{l2} e m sl)