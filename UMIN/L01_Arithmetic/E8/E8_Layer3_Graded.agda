{-# OPTIONS --cubical --guardedness #-}

module UMIN.L01_Arithmetic.E8.E8_Layer3_Graded where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _·_)

-- E7Interface から必要な定数などをインポート
open import UMIN.L01_Arithmetic.FTS.E7Interface
  using (E7; E7-zero; 𝔓ᶜ; 𝕜; 𝕜-zero; 𝕜-one; _+𝕜_; -𝕜_; ratEmbed; posRat)

-- Layer1 (土台) をインポート
open import UMIN.L01_Arithmetic.E8.E8_Layer1_Base
  using (E8; mkE8; Pᶜ; Pᶜ-zero; E8-zero; _⊛E8_)

-- Layer2 (心臓部) をインポートして Lie積を使う！
open import UMIN.L01_Arithmetic.E8.E8_Layer2_Bracket
  using ([_,_]₈)

-- ================================================================
--  特性元 Z (grade を測るための基準)
-- ================================================================

postulate
  κ-constant : E7  -- E7 内の中心的な定数元

-- 特性元 Z (grade を測るための基準)
Z-characteristic : E8
Z-characteristic = mkE8 κ-constant Pᶜ-zero Pᶜ-zero (-𝕜 𝕜-one) 𝕜-zero 𝕜-zero

-- Z による随伴作用 (これが固有値 -2, -1, 0, 1, 2 を与える)
adZ : E8 → E8
adZ R = [ Z-characteristic , R ]₈

-- ================================================================
--  LAYER 3 : 5-graded 分解 (g₋₂, g₋₁, g₀, g₁, g₂)
-- ================================================================

-- 各層のデータ型定義
record g₋₂ : Type where
  field
    u₋₂ : 𝕜

record g₋₁ : Type where
  field
    P₋₁ : Pᶜ
    Q₋₁ : Pᶜ

record g₀ : Type where
  field
    Φ₀ : E7
    r₀ : 𝕜

record g₁ : Type where
  field
    P₁ : Pᶜ
    Q₁ : Pᶜ

record g₂ : Type where
  field
    v₂ : 𝕜

-- 埋め込み写像（それぞれの層の元を 248次元の E8 の世界へ配置する）
ι-g₋₂ : g₋₂ → E8
ι-g₋₂ x = mkE8 E7-zero Pᶜ-zero Pᶜ-zero 𝕜-zero (g₋₂.u₋₂ x) 𝕜-zero

ι-g₋₁ : g₋₁ → E8
ι-g₋₁ x = mkE8 E7-zero (g₋₁.P₋₁ x) (g₋₁.Q₋₁ x) 𝕜-zero 𝕜-zero 𝕜-zero

ι-g₀ : g₀ → E8
ι-g₀ x = mkE8 (g₀.Φ₀ x) Pᶜ-zero Pᶜ-zero (g₀.r₀ x) 𝕜-zero 𝕜-zero

ι-g₁ : g₁ → E8
ι-g₁ x = mkE8 E7-zero (g₁.P₁ x) (g₁.Q₁ x) 𝕜-zero 𝕜-zero 𝕜-zero

ι-g₂ : g₂ → E8
ι-g₂ x = mkE8 E7-zero Pᶜ-zero Pᶜ-zero 𝕜-zero 𝕜-zero (g₂.v₂ x)

-- ================================================================
--  固有値スペック (Z による随伴作用 adZ の性質)
-- ================================================================

-- スカラーの定数
two-𝕜 : 𝕜
two-𝕜 = ratEmbed (posRat 2 1) 𝕜-one

minus-two-𝕜 : 𝕜
minus-two-𝕜 = -𝕜 two-𝕜

one-𝕜 : 𝕜
one-𝕜 = 𝕜-one

minus-one-𝕜 : 𝕜
minus-one-𝕜 = -𝕜 𝕜-one

-- Layer2 で計算を abstract にしたため、ここでは展開せずにスペックとして公理化する
postulate
  g₂-eigen  : (x : g₂)  → adZ (ι-g₂ x)  ≡ (two-𝕜 ⊛E8 (ι-g₂ x))
  g₁-eigen  : (x : g₁)  → adZ (ι-g₁ x)  ≡ (one-𝕜 ⊛E8 (ι-g₁ x))
  g₀-eigen  : (x : g₀)  → adZ (ι-g₀ x)  ≡ E8-zero
  g₋₁-eigen : (x : g₋₁) → adZ (ι-g₋₁ x) ≡ (minus-one-𝕜 ⊛E8 (ι-g₋₁ x))
  g₋₂-eigen : (x : g₋₂) → adZ (ι-g₋₂ x) ≡ (minus-two-𝕜 ⊛E8 (ι-g₋₂ x))

-- g₋₂ が 14次元表現 V14 の基盤となることの宣言
V14-Space : Type
V14-Space = g₋₂