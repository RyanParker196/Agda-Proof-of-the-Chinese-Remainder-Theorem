module final where
open import Basics002

record 𝔾 (element : Set) : Set where
  field
    size : ℕ
    op  : element → element → element
    ε   : element

--improper implementaion of subraction with Nats
-- write down type of alg fixed to natural numbers
-- do CTR just for nats then resume general group stuff
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
-- use ≡? bunch of lemmas
mod : ℕ → ℕ → ℕ
mod x y with x ∸ y |  x ≡? y
mod x y | Pos pos | I = 0
mod x y | Pos pos | O = y - (x × pos)
mod x y | NegS neg | l = x

_ : mod 5 5 ≡ 0
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

--tests
_ : let g = g1
    in order g1 ≡ 1
_ = ↯
