module final where
open import Basics002

record 𝔾 (element : Set) : Set where
  field
    size : ℕ
    op  : element → element → element
    ε   : element

--improper implementaion of subraction with Nats
_-_ : ℕ → ℕ → ℕ
Z - Z = Z
Z - S y = Z
S x - Z = S x
S x - S y = x - y

equal : ℕ → ℕ → 𝔹
equal Z Z = I
equal Z (S y) = O
equal (S x) Z = O
equal (S x) (S y) = equal x y

mod : ℕ → ℕ → ℕ
mod x y with x ∸ y | x ≡? y
mod x y | Pos pos | I = 0
mod x y | Pos pos | O = {!!}
mod x y | NegS neg | l = x

_ : mod 5 3 ≡ 2
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

gcd2 : ℕ → ℕ → ℕ
gcd2 x y with (mod x y) ≡? 0
gcd2 x y | I = {!mod 5 3 ≡? 0!}
gcd2 x y | O with mod x y
… | H with (mod y (y - H)) ≡? 0
gcd2 x y | O | H | I = H
gcd2 x y | O | H | O = H

gcd : ℕ → ℕ → ℕ
gcd x y with x ≤? y
--TODO:
gcd x y | [≤] = gcd2 y x
gcd x y | [>] = gcd2 x y

--gcd test
_ : gcd 5 10 ≡ 5
_ = ↯
_ : gcd 5 3 ≡ 1
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
