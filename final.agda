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
mod x y | g = x - (y × g)


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
gcd x y | [≤] | O = gcd' y x x
gcd x Z | [>] | H = 0
gcd x (S y) | [>] | H = gcd' x (S y) y

_ : gcd 5 7 ≡ 1
_ = ↯
_ : gcd 0 5 ≡ 0
_ = ↯
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
coprime x y = gcd x y ≡? 1

_ : coprime 5 5 ≡ O
_ = ↯
_ : coprime 5 7 ≡ I
_ = ↯
_ : coprime 6 3 ≡ O
_ = ↯
_ : coprime 12 4 ≡ O
_ = ↯
{-
17 ∈ ℤ₃₅ → (2,3) ∈ ℤ₅ × ℤ₇
-}

_! : ℕ → ℕ
_! Z = 1
_! (S x) = (S x) × (x !)

_ : 3 ! ≡ 6
_ = ↯

--Wrote this using wilsons theorem
prime : ℕ → 𝔹
prime Z = O
prime (S Z) = O
prime (S (S x)) = let x = S (S x) in (mod ((x - 1) !) x) ≡? ((x - 1))

_ : prime 7 ≡ I
_ = ↯
_ : prime 4 ≡ O
_ = ↯
_ : prime 3 ≡ I
_ = ↯
_ : prime 5 ≡ I
_ = ↯
_ : prime 0 ≡ O
_ = ↯
_ : prime 1 ≡ O
_ = ↯
_ : prime 5 ≡ I
_ = ↯



postulate
  wilsonsTHM : ∀ (n : ℕ) → prime n ≡ I → mod ((n - 1) ! ) n  ≡ (n - 1)

-- wilsonsTHM n p = {!   !}
-- --tests
-- _ : order g1 ≡ 1
-- _ = ↯

prods : ∀ {n} (xs : vec[ n ] ℕ) → ℕ
prods [] = 1
prods [ x ] = x
prods (x₁ ∷ x₂ ∷ xs) = x₁ × x₂ × prods xs

_ : let xs = [ 3 , 2 ] in prods xs ≡ 6 
_ = ↯

base-case : (a : ℕ) (m : ℕ) → (i : idx 1) → mod a ([ m ] #[ i ]) ≡ mod ([ a ] #[ i ]) ([ m ] #[ i ])
base-case a m Z = ↯
base-case a m (S ())

help : ∀ {k : ℕ} (i : idx k) → idx (S k)
help {Z} ()
help {S k} i with idx (k)
… | H = S i

postulate
  BezID : ∀ (m1 m2 : ℕ) → coprime m1 m2 ≡ I → vec[ 2 ] ℕ
  helper : ∀ {m1 m2 k : ℕ} {ms : vec[ k ] ℕ} (i j : idx (S (S k)))
    → ¬ i ≡ j
    → coprime ((m1 ∷ m2 ∷ ms) #[ i ]) ((m1 ∷ m2 ∷ ms) #[ j ]) ≡ I
    → ∃ m1 ⦂ ℕ ST ∃ m2 ⦂ ℕ ST coprime m1 m2 ≡ I
  triv : Z ≡? S Z ≡ I → 𝟘
  fake : O ≡ I
  Lemma : ∀ {k : ℕ} (i j : idx k) → (¬ i ≡ j) → ¬ help i ≡ help j
  
algo : ℕ → ℕ → (m1 : ℕ) → (m2 : ℕ) → coprime m1 m2 ≡ I → ℕ
algo a1 a2 m1 m2 copP with BezID m1 m2 copP
algo a1 a2 m1 m2 copP | [ n₁ , n₂ ] = (a1 × m2 × n₂) + (a2 × m1 × n₁)




CRT-1 :
  ∀ k
    (a : vec[ k ] ℕ)
    (m : vec[ k ] ℕ)
  -- k > 1
  → 0 < k
  -- coprime assumption
  -- i ≠ j ⇒ (mᵢ,mⱼ) = 1
  → (∀ (i j : idx k) → ¬ (i ≡ j) → coprime (m #[ i ]) (m #[ j ]) ≡ I)
  -- x is the solution to the system of congruences
  → ∃ x ⦂ ℕ ST
  -- x ≡ aᵢ (mod mᵢ)
    (∀ (i : idx k) → mod x (m #[ i ]) ≡ mod (a #[ i ]) (m #[ i ]))
CRT-1 0 a m () copP
CRT-1 1 [ a ] [ m ] ltP copP = ⟨∃ a , base-case a m ⟩
CRT-1 (S (S k)) (a1 ∷ a2 ∷ as) (m1 ∷ m2 ∷ ms) ltP copP
  with CRT-1 (S k) (algo a1 a2 m1 m2 (copP Z (S Z) λ x → triv fake) ∷ as) (m1 × m2 ∷ ms) Z λ i j x → copP ({!help i!}) ({!!}) ({!!})
CRT-1 (S (S k)) (a1 ∷ a2 ∷ as) (m1 ∷ m2 ∷ ms) ltP copP | ⟨∃ x , cong ⟩ = ⟨∃ x , (λ i → {!!}) ⟩

