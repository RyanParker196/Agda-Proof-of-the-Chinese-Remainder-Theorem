module final where
open import Basics002

record 𝔾 (element : Set) : Set where
  field
    size : ℕ
    op  : element → element → element
    ε   : element

_-_ : ℕ → ℕ → ℕ
Z - Z = Z
Z - S y = Z
S x - Z = S x
S x - S y = x - y

--div' : ℕ → ℕ → ℕ → ℕ
--div' Z y Z = 1
--div' Z y (S a) = a
--div' (S x) y a = div' ((S x) - y) y (S a)
--
--_div_ : ℕ → ℕ → ℕ
--_div_ x y with x ≤? y | x ≡? y
--_div_ x y | [≤] | I = 1
--_div_ x y | [≤] | O = 0
--_div_ x y | [>] | H = {!div' x y 1!}

{-# TERMINATING #-}
div' : ℕ → ℕ → ℕ → ℕ
div' x y a with x ≤? y | x ≡? y
div' x y a | [≤] | I = S a
div' x y a | [≤] | O = a
div' x y a | [>] | H = div' (x - y) y (S a)

_div_ : ℕ → ℕ → ℕ
Z div Z = Z
Z div S y = Z
S x div Z = Z
S x div S y = div' (S x) (S y) 0

_ : 5 div 3 ≡ 1
_ = ↯

_ : 10 div 5 ≡ 2
_ = ↯

_ : 14 div 4 ≡ 3
_ = ↯

_ : 0 div 5 ≡ 0
_ = ↯

_ : 12 div 5 ≡ 2
_ = ↯

equal : ℕ → ℕ → 𝔹
equal Z Z = I
equal Z (S y) = O
equal (S x) Z = O
equal (S x) (S y) = equal x y

mod : ℕ → ℕ → ℕ
mod x y with x div y
mod x y | g = {!x - (y × g)!}


_ : mod 5 3 ≡ 2
_ = ↯

_ : mod 14 4 ≡ 2
_ = ↯

_ : mod 0 5 ≡ 0
_ = ↯

_ : mod 10 5 ≡ 0
_ = ↯

_ : mod 2 5 ≡ 2
_ = ↯

--Constructs group with: element   =  1
--                       operation = {+}
g1 : 𝔾 ℕ
g1 = record { op = λ x1 x2 → x1 + x2 ; ε = 0 ; size = 1 }

--funtion to return order of a group
order : 𝔾 ℕ → ℕ
order record { size = size ; op = op ; ε = ε } = size

data Maybe {a} (A : Set a) : Set a where
  just    : (x : A) → Maybe A
  nothing : Maybe A
  
is-just : ∀ {a} {A : Set a} → Maybe A → 𝔹
is-just (just _) = I
is-just nothing  = O

is-nothing : ∀ {a} {A : Set a} → Maybe A → 𝔹
is-nothing (just x) = O
is-nothing nothing = I


gcd' : ℕ → ℕ → ℕ → ℕ
gcd' x y a with mod x a ≡? 0 | mod x a ≡? 0
gcd' x y a | I | I = a
gcd' x y Z | I | O = Z
gcd' x y (S a) | I | O = gcd' x y a
gcd' x y Z | O | I = Z
gcd' x y (S a) | O | I = gcd' x y a
gcd' x y Z | O | O = Z
gcd' x y (S a) | O | O = gcd' x y a


gcd : ℕ → ℕ → ℕ
gcd x y with x ≤? y | x ≡? y
gcd x y | [≤] | I = x
gcd x y | [≤] | O = {!gcd' y x x!}
gcd x Z | [>] | H = 0
gcd x (S y) | [>] | H = gcd' x (S y) y

--_ : gcd 5 7 ≡ 1
--_ = ↯
--_ : gcd 0 5 ≡ 0
--_ = ↯
--_ : gcd 5 0 ≡ 0
--_ = ↯
--_ : gcd 5 10 ≡ 5
--_ = ↯
--_ : gcd 21 6 ≡ 3
--_ = ↯
--_ : gcd 5 3 ≡ 1
--_ = ↯
--_ : gcd 6 2 ≡ 1
--_ = ↯

coprime : ℕ → ℕ → 𝔹
coprime x y with gcd x y ≡ 1
… | H = {!!}


_ : coprime 5 7 ≡ I
_ = ↯
_ : coprime 6 3 ≡ O
_ = ↯
_ : coprime 12 4 ≡ O
_ = ↯
{-
17 ∈ ℤ₃₅ → (2,3) ∈ ℤ₅ × ℤ₇
-}
--CRT : 

--tests
_ : order g1 ≡ 1
_ = ↯
