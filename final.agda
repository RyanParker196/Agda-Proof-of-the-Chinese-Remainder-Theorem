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

{-# TERMINATING #-}
div' : ℕ → ℕ → ℕ → ℕ
div' Z y a = a
div' (S x) y a = div' (x - y) y (S a)

_div_ : ℕ → ℕ → ℕ
_div_ x y with x ≤? y | x ≡? y
_div_ x y | [≤] | I = 1
_div_ x y | [≤] | O = 0
_div_ x y | [>] | H = div' x y 0

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

{-# TERMINATING #-}
mod : ℕ → ℕ → ℕ
mod x y with x div y
mod x y | Z = x
mod x y | S g = mod (x - y) y 

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


{-# TERMINATING #-}
gcd' : ℕ → ℕ → ℕ → ℕ
gcd' Z y a = a
gcd' (S x) y a with mod x a ≡? 0 | mod x a ≡? 0
gcd' (S x) y a | I | I = {!a!}
gcd' (S x) y a | I | O = {!!}
gcd' (S x) y a | O | I = {!!}
gcd' (S x) y a | O | O = {!!}

--gcd' x y a with mod x a ≡? 0 | mod y a ≡? 0

gcd : ℕ → ℕ → ℕ
gcd x y with x ≤? y | x ≡? y
gcd x y | [≤] | I = Z
gcd x y | [≤] | O = x
gcd x y | [>] | H = gcd' x y y
--gcd' x y y

_ : gcd 5 0 ≡ 0
_ = ↯
_ : gcd 5 10 ≡ 5
_ = ↯
_ : gcd 21 6 ≡ 3
_ = ↯
_ : gcd 5 3 ≡ 1
_ = ↯
_ : gcd 6 2 ≡ 1
_ = ↯

coprime : ℕ → ℕ → 𝔹
coprime x y = {!!}
{-
17 ∈ ℤ₃₅ → (2,3) ∈ ℤ₅ × ℤ₇
-}
--CRT : 

--tests
_ : order g1 ≡ 1
_ = ↯
