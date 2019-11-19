module final where
open import Basics002

record 𝔾 (element : Set) : Set where
  field
    size : ℕ
    op  : element → element → element
    ε   : element

identity : ∀ (s : ℕ) → (op : ℕ → ℕ → ℕ) → ℕ
identity s op = s

g1 : 𝔾 ℕ
g1 = record { op = λ x1 x2 → x1 + x2 ; ε = 0 ; size = 1 }

order : 𝔾 ℕ → ℕ
order record { size = size ; op = op ; ε = ε } = size

_ : let g : 𝔾 ℕ
        g = g1
    in order g1 ≡ 1
_ = ↯
