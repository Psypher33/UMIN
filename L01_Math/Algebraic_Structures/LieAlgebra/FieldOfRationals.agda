{-# OPTIONS --cubical --guardedness #-}

-- ================================================================
-- §0. Field of Rationals (𝕜 = ℚ)
-- ================================================================

module UMIN.L01_Math.Algebraic_Structures.LieAlgebra.FieldOfRationals where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _·_)
open import Cubical.Data.Int renaming (_+_ to _+ℤ_; _·_ to _·ℤ_; -_ to -ℤ_)

-- 正の有理数（E8LieAlgebra の ℚ⁺ と同一）
record ℚ⁺ : Type where
  constructor _//_
  field
    num : ℕ
    den : ℕ
open ℚ⁺

-- ℕ×ℕ から ℚ⁺ を構築（E7Interface 等で 2/3, 1/3 等を 𝕜 に埋め込む用）
posRat : ℕ → ℕ → ℚ⁺
posRat n d = record { num = n ; den = d }

_≡ᵣ_ : ℚ⁺ → ℚ⁺ → Type
(a // b) ≡ᵣ (c // d) = a · d ≡ b · c

-- 符号付き有理数
record ℚ : Type where
  constructor _//_
  field
    num : ℤ
    den : ℕ
open ℚ

-- 𝕜 の具体化
𝕜 : Type
𝕜 = ℚ

𝕜-zero : 𝕜
𝕜-zero = (pos 0) // 1

𝕜-one : 𝕜
𝕜-one = (pos 1) // 1

-- スカラー演算の具体的実装（簡約化は一旦省略）
_+𝕜_ : 𝕜 → 𝕜 → 𝕜
(n₁ // d₁) +𝕜 (n₂ // d₂) = (n₁ ·ℤ pos d₂ +ℤ n₂ ·ℤ pos d₁) // (d₁ · d₂)

_·𝕜_ : 𝕜 → 𝕜 → 𝕜
(n₁ // d₁) ·𝕜 (n₂ // d₂) = (n₁ ·ℤ n₂) // (d₁ · d₂)

-𝕜_ : 𝕜 → 𝕜
-𝕜_ (n // d) = (-ℤ n) // d

infixl 20 _+𝕜_
infixl 30 _·𝕜_

-- 有理数埋め込み（ℚ⁺ を 𝕜 に変換してスカラー倍する）
ratEmbed : ℚ⁺ → 𝕜 → 𝕜
ratEmbed (qn // qd) (kn // kd) = (pos qn ·ℤ kn) // (qd · kd)
