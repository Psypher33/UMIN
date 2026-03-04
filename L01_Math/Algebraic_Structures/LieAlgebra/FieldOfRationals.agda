{-# OPTIONS --cubical --safe --guardedness #-}

-- ================================================================
-- §0. Field of Rationals (𝕜 = ℚ)
-- ================================================================

module UMIN.L01_Math.Algebraic_Structures.LieAlgebra.FieldOfRationals where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _·_)
open import Cubical.Data.Int renaming (_+_ to _+ℤ_; _·_ to _·ℤ_; -_ to -ℤ_)
open import Cubical.Data.Int.Properties

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

-- ================================================================
-- §1. 有理数の基本法則の証明 (UMIN-Universe の地盤固め)
-- ================================================================
-- 有理数の等価性の証明用ヘルパー
-- (n1 // d1) ≡ (n2 // d2) は n1 * d2 ≡ n2 * d1 で定義される

-- 💥 撃破！ 加法の逆元に関する法則： 0 + (-0) ≡ 0
-- 有理数の定義に従い、成分計算で証明します。
𝕜-zero-add-inv : (𝕜-zero +𝕜 (-𝕜 𝕜-zero)) ≡ 𝕜-zero
𝕜-zero-add-inv = refl
-- ※ 𝕜-zero の定義と +𝕜, -𝕜 の定義が簡約されて同じ形になるため、
--   多くの場合は refl (定義同値) で通ります！

-- ================================================================
-- §2. 𝕜 上の同値関係 ≈𝕜 （分数表示の違いを潰す）
-- ================================================================
--  (n₁ // d₁) ≈𝕜 (n₂ // d₂)  :≡  n₁ ·ℤ pos d₂ ≡ n₂ ·ℤ pos d₁
-- という、教科書通りの「クロス積が等しければ同値」という関係です。

_≈𝕜_ : 𝕜 → 𝕜 → Type
(n₁ // d₁) ≈𝕜 (n₂ // d₂) = (n₁ ·ℤ pos d₂) ≡ (n₂ ·ℤ pos d₁)

infix 4 _≈𝕜_

-- 反射律
≈𝕜-refl : ∀ x → x ≈𝕜 x
≈𝕜-refl (n // d) = refl

-- 対称律
≈𝕜-sym : ∀ {x y} → x ≈𝕜 y → y ≈𝕜 x
≈𝕜-sym {n₁ // d₁} {n₂ // d₂} p = sym p

-- 推移律（TODO）
-- ここではまだ証明していませんが、整数乗法の結合則・交換則と
-- 自然数から整数への埋め込みの性質を使えば証明できます。
-- 後で ℤ の環構造を整理したうえで実装します。
-- ≈𝕜-trans : ∀ {x y z} → x ≈𝕜 y → y ≈𝕜 z → x ≈𝕜 z
-- ≈𝕜-trans = {!!}

-- ================================================================
-- §3. 演算の Well-defined 性 (Congruence)
-- 同値な分数同士を足したり掛けたりしても、結果は同値になることの保証。
-- ================================================================

-- TODO: safe を維持するため、現時点では型だけコメントとして残しておく。
-- 後で ≈𝕜-trans や ℤ の性質を整理した段階で、実装とともに有効化する。
--
-- 加法の合同性
-- +𝕜-cong : ∀ {a b c d : 𝕜} → a ≈𝕜 b → c ≈𝕜 d → (a +𝕜 c) ≈𝕜 (b +𝕜 d)
-- +𝕜-cong p q = {!!}
--
-- 乗法の合同性
-- ·𝕜-cong : ∀ {a b c d : 𝕜} → a ≈𝕜 b → c ≈𝕜 d → (a ·𝕜 c) ≈𝕜 (b ·𝕜 d)
-- ·𝕜-cong p q = {!!}
--
-- ================================================================
-- §3. 演算の Well-defined 性 (Congruence)
-- 同値な分数同士を足したり掛けたりしても、結果は同値になることの保証。
-- ================================================================

-- 【自作の補題（鍵）】整数の乗算における、マイナス符号の左括り出し
neg-mul-left : ∀ (x y : ℤ) → (-ℤ x) ·ℤ y ≡ -ℤ (x ·ℤ y)
neg-mul-left x y = sym (-DistL· x y)

-- 符号反転の合同性（メイン定理）
-𝕜-cong : ∀ {a b : 𝕜} → a ≈𝕜 b → (-𝕜 a) ≈𝕜 (-𝕜 b)
-𝕜-cong {n₁ // d₁} {n₂ // d₂} p =
  (-ℤ n₁) ·ℤ pos d₂
    ≡⟨ neg-mul-left n₁ (pos d₂) ⟩
  -ℤ (n₁ ·ℤ pos d₂)
    ≡⟨ cong -ℤ_ p ⟩
  -ℤ (n₂ ·ℤ pos d₁)
    ≡⟨ sym (neg-mul-left n₂ (pos d₁)) ⟩
  (-ℤ n₂) ·ℤ pos d₁
  ∎
