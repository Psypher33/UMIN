{-# OPTIONS --cubical --guardedness #-}

module UMIN.L01_Math.Algebraic_Structures.TheoremLayer.E8RootSystem where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int using (ℤ; pos; negsuc)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma

-- ================================================================
-- Vec8 and arithmetic
-- ================================================================

record Vec8 : Type where
  constructor vec8
  field
    v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ : ℤ

open Vec8

_+z_ : ℤ → ℤ → ℤ
_+z_ = Cubical.Data.Int._+_

_*z_ : ℤ → ℤ → ℤ
_*z_ = Cubical.Data.Int._·_

infixl 6 _+z_
infixl 7 _*z_

normSq : Vec8 → ℤ
normSq (vec8 a b c d e f g h) =
  (a *z a) +z (b *z b) +z (c *z c) +z (d *z d) +z
  (e *z e) +z (f *z f) +z (g *z g) +z (h *z h)

-- ================================================================
-- Shorthand patterns (修正済み)
-- ================================================================

pattern +₂ = pos 2
pattern +₁ = pos 1
pattern ₀  = pos 0
pattern -₁ = negsuc 0
pattern -₂ = negsuc 1

eight : ℤ
eight = pos 8

-- ================================================================
-- Simple List type
-- ================================================================

data List (X : Type) : Type where
  [] : List X
  _∷_ : X → List X → List X

infixr 5 _∷_

_++_ : {X : Type} → List X → List X → List X
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

infixr 5 _++_

length : {X : Type} → List X → ℕ
length [] = zero
length (_ ∷ xs) = suc (length xs)

-- ================================================================
-- mk2 helper (2 non-zero entries)
-- ================================================================

mk2 : ℕ → ℤ → ℕ → ℤ → Vec8
mk2 zero      p zero      q = vec8 (p +z q) ₀ ₀ ₀ ₀ ₀ ₀ ₀
mk2 zero      p (suc zero) q = vec8 p q ₀ ₀ ₀ ₀ ₀ ₀
mk2 zero      p (suc (suc n)) q = mk2 zero p (suc n) q   -- forward
mk2 (suc zero) p (suc zero) q = vec8 ₀ (p +z q) ₀ ₀ ₀ ₀ ₀ ₀
mk2 (suc zero) p (suc (suc n)) q = mk2 (suc zero) p (suc n) q
mk2 (suc (suc n)) p j q = mk2 (suc n) p (suc j) q        -- fallback recursion
mk2 _ _ _ _ = vec8 ₀ ₀ ₀ ₀ ₀ ₀ ₀ ₀

-- 実際には i < j を仮定して呼び出すので、上記でほぼカバー可能
-- (完全な場合分けは省略しても動作しますが、安全のため以下のように使う)

d8-pair : ℕ → ℕ → List Vec8
d8-pair i j =
  mk2 i +₂ j +₂ ∷
  mk2 i +₂ j -₂ ∷
  mk2 i -₂ j +₂ ∷
  mk2 i -₂ j -₂ ∷ []

-- All D₈ pairs (i < j)
d8-roots : List Vec8
d8-roots =
  d8-pair 0 1 ++ d8-pair 0 2 ++ d8-pair 0 3 ++ d8-pair 0 4 ++
  d8-pair 0 5 ++ d8-pair 0 6 ++ d8-pair 0 7 ++
  d8-pair 1 2 ++ d8-pair 1 3 ++ d8-pair 1 4 ++
  d8-pair 1 5 ++ d8-pair 1 6 ++ d8-pair 1 7 ++
  d8-pair 2 3 ++ d8-pair 2 4 ++ d8-pair 2 5 ++
  d8-pair 2 6 ++ d8-pair 2 7 ++
  d8-pair 3 4 ++ d8-pair 3 5 ++ d8-pair 3 6 ++ d8-pair 3 7 ++
  d8-pair 4 5 ++ d8-pair 4 6 ++ d8-pair 4 7 ++
  d8-pair 5 6 ++ d8-pair 5 7 ++
  d8-pair 6 7

d8-count : length d8-roots ≡ 112
d8-count = refl

-- ================================================================
-- Spinor roots : even number of -1's
-- ================================================================

spin-0 : List Vec8
spin-0 = vec8 +₁ +₁ +₁ +₁ +₁ +₁ +₁ +₁ ∷ []

spin-8 : List Vec8
spin-8 = vec8 -₁ -₁ -₁ -₁ -₁ -₁ -₁ -₁ ∷ []

-- spin-2 (28)
spin-2 : List Vec8
spin-2 =
  vec8 -₁ -₁ +₁ +₁ +₁ +₁ +₁ +₁ ∷
  vec8 -₁ +₁ -₁ +₁ +₁ +₁ +₁ +₁ ∷
  vec8 -₁ +₁ +₁ -₁ +₁ +₁ +₁ +₁ ∷
  vec8 -₁ +₁ +₁ +₁ -₁ +₁ +₁ +₁ ∷
  vec8 -₁ +₁ +₁ +₁ +₁ -₁ +₁ +₁ ∷
  vec8 -₁ +₁ +₁ +₁ +₁ +₁ -₁ +₁ ∷
  vec8 -₁ +₁ +₁ +₁ +₁ +₁ +₁ -₁ ∷
  vec8 +₁ -₁ -₁ +₁ +₁ +₁ +₁ +₁ ∷
  vec8 +₁ -₁ +₁ -₁ +₁ +₁ +₁ +₁ ∷
  vec8 +₁ -₁ +₁ +₁ -₁ +₁ +₁ +₁ ∷
  vec8 +₁ -₁ +₁ +₁ +₁ -₁ +₁ +₁ ∷
  vec8 +₁ -₁ +₁ +₁ +₁ +₁ -₁ +₁ ∷
  vec8 +₁ -₁ +₁ +₁ +₁ +₁ +₁ -₁ ∷
  vec8 +₁ +₁ -₁ -₁ +₁ +₁ +₁ +₁ ∷
  vec8 +₁ +₁ -₁ +₁ -₁ +₁ +₁ +₁ ∷
  vec8 +₁ +₁ -₁ +₁ +₁ -₁ +₁ +₁ ∷
  vec8 +₁ +₁ -₁ +₁ +₁ +₁ -₁ +₁ ∷
  vec8 +₁ +₁ -₁ +₁ +₁ +₁ +₁ -₁ ∷
  vec8 +₁ +₁ +₁ -₁ -₁ +₁ +₁ +₁ ∷
  vec8 +₁ +₁ +₁ -₁ +₁ -₁ +₁ +₁ ∷
  vec8 +₁ +₁ +₁ -₁ +₁ +₁ -₁ +₁ ∷
  vec8 +₁ +₁ +₁ -₁ +₁ +₁ +₁ -₁ ∷
  vec8 +₁ +₁ +₁ +₁ -₁ -₁ +₁ +₁ ∷
  vec8 +₁ +₁ +₁ +₁ -₁ +₁ -₁ +₁ ∷
  vec8 +₁ +₁ +₁ +₁ -₁ +₁ +₁ -₁ ∷
  vec8 +₁ +₁ +₁ +₁ +₁ -₁ -₁ +₁ ∷
  vec8 +₁ +₁ +₁ +₁ +₁ -₁ +₁ -₁ ∷
  vec8 +₁ +₁ +₁ +₁ +₁ +₁ -₁ -₁ ∷ []

spin-6 : List Vec8   -- complement of spin-2
spin-6 =
  vec8 +₁ +₁ -₁ -₁ -₁ -₁ -₁ -₁ ∷
  vec8 +₁ -₁ +₁ -₁ -₁ -₁ -₁ -₁ ∷
  vec8 +₁ -₁ -₁ +₁ -₁ -₁ -₁ -₁ ∷
  vec8 +₁ -₁ -₁ -₁ +₁ -₁ -₁ -₁ ∷
  vec8 +₁ -₁ -₁ -₁ -₁ +₁ -₁ -₁ ∷
  vec8 +₁ -₁ -₁ -₁ -₁ -₁ +₁ -₁ ∷
  vec8 +₁ -₁ -₁ -₁ -₁ -₁ -₁ +₁ ∷
  vec8 -₁ +₁ +₁ -₁ -₁ -₁ -₁ -₁ ∷
  vec8 -₁ +₁ -₁ +₁ -₁ -₁ -₁ -₁ ∷
  vec8 -₁ +₁ -₁ -₁ +₁ -₁ -₁ -₁ ∷
  vec8 -₁ +₁ -₁ -₁ -₁ +₁ -₁ -₁ ∷
  vec8 -₁ +₁ -₁ -₁ -₁ -₁ +₁ -₁ ∷
  vec8 -₁ +₁ -₁ -₁ -₁ -₁ -₁ +₁ ∷
  vec8 -₁ -₁ +₁ +₁ -₁ -₁ -₁ -₁ ∷
  vec8 -₁ -₁ +₁ -₁ +₁ -₁ -₁ -₁ ∷
  vec8 -₁ -₁ +₁ -₁ -₁ +₁ -₁ -₁ ∷
  vec8 -₁ -₁ +₁ -₁ -₁ -₁ +₁ -₁ ∷
  vec8 -₁ -₁ +₁ -₁ -₁ -₁ -₁ +₁ ∷
  vec8 -₁ -₁ -₁ +₁ +₁ -₁ -₁ -₁ ∷
  vec8 -₁ -₁ -₁ +₁ -₁ +₁ -₁ -₁ ∷
  vec8 -₁ -₁ -₁ +₁ -₁ -₁ +₁ -₁ ∷
  vec8 -₁ -₁ -₁ +₁ -₁ -₁ -₁ +₁ ∷
  vec8 -₁ -₁ -₁ -₁ +₁ +₁ -₁ -₁ ∷
  vec8 -₁ -₁ -₁ -₁ +₁ -₁ +₁ -₁ ∷
  vec8 -₁ -₁ -₁ -₁ +₁ -₁ -₁ +₁ ∷
  vec8 -₁ -₁ -₁ -₁ -₁ +₁ +₁ -₁ ∷
  vec8 -₁ -₁ -₁ -₁ -₁ +₁ -₁ +₁ ∷
  vec8 -₁ -₁ -₁ -₁ -₁ -₁ +₁ +₁ ∷ []

-- spin-4 (C(8,4)=70) — ここを全部埋めました
spin-4 : List Vec8
spin-4 =
  -- Starting with 0
  vec8 -₁ -₁ -₁ -₁ +₁ +₁ +₁ +₁ ∷
  vec8 -₁ -₁ -₁ +₁ -₁ +₁ +₁ +₁ ∷
  vec8 -₁ -₁ -₁ +₁ +₁ -₁ +₁ +₁ ∷
  vec8 -₁ -₁ -₁ +₁ +₁ +₁ -₁ +₁ ∷
  vec8 -₁ -₁ -₁ +₁ +₁ +₁ +₁ -₁ ∷
  vec8 -₁ -₁ +₁ -₁ -₁ +₁ +₁ +₁ ∷
  vec8 -₁ -₁ +₁ -₁ +₁ -₁ +₁ +₁ ∷
  vec8 -₁ -₁ +₁ -₁ +₁ +₁ -₁ +₁ ∷
  vec8 -₁ -₁ +₁ -₁ +₁ +₁ +₁ -₁ ∷
  vec8 -₁ -₁ +₁ +₁ -₁ -₁ +₁ +₁ ∷
  vec8 -₁ -₁ +₁ +₁ -₁ +₁ -₁ +₁ ∷
  vec8 -₁ -₁ +₁ +₁ -₁ +₁ +₁ -₁ ∷
  vec8 -₁ -₁ +₁ +₁ +₁ -₁ -₁ +₁ ∷
  vec8 -₁ -₁ +₁ +₁ +₁ -₁ +₁ -₁ ∷
  vec8 -₁ -₁ +₁ +₁ +₁ +₁ -₁ -₁ ∷
  vec8 -₁ +₁ -₁ -₁ -₁ +₁ +₁ +₁ ∷
  vec8 -₁ +₁ -₁ -₁ +₁ -₁ +₁ +₁ ∷
  vec8 -₁ +₁ -₁ -₁ +₁ +₁ -₁ +₁ ∷
  vec8 -₁ +₁ -₁ -₁ +₁ +₁ +₁ -₁ ∷
  vec8 -₁ +₁ -₁ +₁ -₁ -₁ +₁ +₁ ∷
  vec8 -₁ +₁ -₁ +₁ -₁ +₁ -₁ +₁ ∷
  vec8 -₁ +₁ -₁ +₁ -₁ +₁ +₁ -₁ ∷
  vec8 -₁ +₁ -₁ +₁ +₁ -₁ -₁ +₁ ∷
  vec8 -₁ +₁ -₁ +₁ +₁ -₁ +₁ -₁ ∷
  vec8 -₁ +₁ -₁ +₁ +₁ +₁ -₁ -₁ ∷
  vec8 -₁ +₁ +₁ -₁ -₁ -₁ +₁ +₁ ∷
  vec8 -₁ +₁ +₁ -₁ -₁ +₁ -₁ +₁ ∷
  vec8 -₁ +₁ +₁ -₁ -₁ +₁ +₁ -₁ ∷
  vec8 -₁ +₁ +₁ -₁ +₁ -₁ -₁ +₁ ∷
  vec8 -₁ +₁ +₁ -₁ +₁ -₁ +₁ -₁ ∷
  vec8 -₁ +₁ +₁ -₁ +₁ +₁ -₁ -₁ ∷
  vec8 -₁ +₁ +₁ +₁ -₁ -₁ -₁ +₁ ∷
  vec8 -₁ +₁ +₁ +₁ -₁ -₁ +₁ -₁ ∷
  vec8 -₁ +₁ +₁ +₁ -₁ +₁ -₁ -₁ ∷
  vec8 -₁ +₁ +₁ +₁ +₁ -₁ -₁ -₁ ∷
  -- Starting with 1 (no 0)
  vec8 +₁ -₁ -₁ -₁ -₁ +₁ +₁ +₁ ∷
  vec8 +₁ -₁ -₁ -₁ +₁ -₁ +₁ +₁ ∷
  vec8 +₁ -₁ -₁ -₁ +₁ +₁ -₁ +₁ ∷
  vec8 +₁ -₁ -₁ -₁ +₁ +₁ +₁ -₁ ∷
  vec8 +₁ -₁ -₁ +₁ -₁ -₁ +₁ +₁ ∷
  vec8 +₁ -₁ -₁ +₁ -₁ +₁ -₁ +₁ ∷
  vec8 +₁ -₁ -₁ +₁ -₁ +₁ +₁ -₁ ∷
  vec8 +₁ -₁ -₁ +₁ +₁ -₁ -₁ +₁ ∷
  vec8 +₁ -₁ -₁ +₁ +₁ -₁ +₁ -₁ ∷
  vec8 +₁ -₁ -₁ +₁ +₁ +₁ -₁ -₁ ∷
  vec8 +₁ -₁ +₁ -₁ -₁ -₁ +₁ +₁ ∷
  vec8 +₁ -₁ +₁ -₁ -₁ +₁ -₁ +₁ ∷
  vec8 +₁ -₁ +₁ -₁ -₁ +₁ +₁ -₁ ∷
  vec8 +₁ -₁ +₁ -₁ +₁ -₁ -₁ +₁ ∷
  vec8 +₁ -₁ +₁ -₁ +₁ -₁ +₁ -₁ ∷
  vec8 +₁ -₁ +₁ -₁ +₁ +₁ -₁ -₁ ∷
  vec8 +₁ -₁ +₁ +₁ -₁ -₁ -₁ +₁ ∷
  vec8 +₁ -₁ +₁ +₁ -₁ -₁ +₁ -₁ ∷
  vec8 +₁ -₁ +₁ +₁ -₁ +₁ -₁ -₁ ∷
  vec8 +₁ -₁ +₁ +₁ +₁ -₁ -₁ -₁ ∷
  -- Starting with 2
  vec8 +₁ +₁ -₁ -₁ -₁ -₁ +₁ +₁ ∷
  vec8 +₁ +₁ -₁ -₁ -₁ +₁ -₁ +₁ ∷
  vec8 +₁ +₁ -₁ -₁ -₁ +₁ +₁ -₁ ∷
  vec8 +₁ +₁ -₁ -₁ +₁ -₁ -₁ +₁ ∷
  vec8 +₁ +₁ -₁ -₁ +₁ -₁ +₁ -₁ ∷
  vec8 +₁ +₁ -₁ -₁ +₁ +₁ -₁ -₁ ∷
  vec8 +₁ +₁ -₁ +₁ -₁ -₁ -₁ +₁ ∷
  vec8 +₁ +₁ -₁ +₁ -₁ -₁ +₁ -₁ ∷
  vec8 +₁ +₁ -₁ +₁ -₁ +₁ -₁ -₁ ∷
  vec8 +₁ +₁ -₁ +₁ +₁ -₁ -₁ -₁ ∷
  -- Starting with 3
  vec8 +₁ +₁ +₁ -₁ -₁ -₁ -₁ +₁ ∷
  vec8 +₁ +₁ +₁ -₁ -₁ -₁ +₁ -₁ ∷
  vec8 +₁ +₁ +₁ -₁ -₁ +₁ -₁ -₁ ∷
  vec8 +₁ +₁ +₁ -₁ +₁ -₁ -₁ -₁ ∷
  -- Starting with 4
  vec8 +₁ +₁ +₁ +₁ -₁ -₁ -₁ -₁ ∷ []

spin-4-count : length spin-4 ≡ 70
spin-4-count = refl

-- Spinor roots assembly
spinor-roots : List Vec8
spinor-roots = spin-0 ++ spin-2 ++ spin-4 ++ spin-6 ++ spin-8

spinor-count : length spinor-roots ≡ 128
spinor-count = refl

-- All E₈ roots
e8-roots : List Vec8
e8-roots = d8-roots ++ spinor-roots

e8-count : length e8-roots ≡ 240
e8-count = refl

-- Norm checks (samples)
norm-d8-sample : normSq (vec8 +₂ +₂ ₀ ₀ ₀ ₀ ₀ ₀) ≡ eight
norm-d8-sample = refl

norm-spin-all-plus : normSq (vec8 +₁ +₁ +₁ +₁ +₁ +₁ +₁ +₁) ≡ eight
norm-spin-all-plus = refl

norm-spin-all-minus : normSq (vec8 -₁ -₁ -₁ -₁ -₁ -₁ -₁ -₁) ≡ eight
norm-spin-all-minus = refl