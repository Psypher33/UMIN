{-# OPTIONS --cubical --guardedness #-}

module UMIN.L01_Math.Algebraic_Structures.LieAlgebra.E8_Layer1_Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _·_)

-- E7Interface から基礎的な型と線形演算のみをインポート（括弧積 [_,_]₇ などはまだ呼ばない）
open import UMIN.L01_Math.Algebraic_Structures.LieAlgebra.E7Interface
  as E7Int using (E7; E7-zero; 𝔓ᶜ; mk𝔓; _+E7_; -E7_; _⊛E7_; 𝕜; 𝕜-zero; 𝕜-one; _+𝕜_; _·𝕜_; -𝕜_; ratEmbed; posRat; ℚ⁺; _//_)
import UMIN.L01_Math.Algebraic_Structures.LieAlgebra.AlbertAlgebra as AlbertAlg

-- ================================================================
--  LAYER 1 : Pᶜ (𝔓ᶜ) 空間と基本演算
-- ================================================================

Pᶜ : Type
Pᶜ = 𝔓ᶜ

-- 𝔍ᶜ の零元
𝔍-zero : AlbertAlg.𝔍ᶜ
𝔍-zero = AlbertAlg.mk𝔍 𝕜-zero 𝕜-zero 𝕜-zero AlbertAlg.𝕆-zero AlbertAlg.𝕆-zero AlbertAlg.𝕆-zero

Pᶜ-zero : Pᶜ
Pᶜ-zero = mk𝔓 𝔍-zero 𝔍-zero 𝕜-zero 𝕜-zero

_+P_ : Pᶜ → Pᶜ → Pᶜ
mk𝔓 X₁ Y₁ ξ₁ η₁ +P mk𝔓 X₂ Y₂ ξ₂ η₂ = 
  mk𝔓 (AlbertAlg._+𝔍_ X₁ X₂) (AlbertAlg._+𝔍_ Y₁ Y₂) (ξ₁ +𝕜 ξ₂) (η₁ +𝕜 η₂)

-P_ : Pᶜ → Pᶜ
-P (mk𝔓 X Y ξ η) = 
  mk𝔓 (AlbertAlg.-𝔍_ X) (AlbertAlg.-𝔍_ Y) (-𝕜 ξ) (-𝕜 η)

_⊛P_ : 𝕜 → Pᶜ → Pᶜ
k ⊛P (mk𝔓 X Y ξ η) = 
  mk𝔓 (AlbertAlg._⊛𝔍_ k X) (AlbertAlg._⊛𝔍_ k Y) (k ·𝕜 ξ) (k ·𝕜 η)

-- Pᶜ 用の演算子優先順位
infixl 20 _+P_
infix  25 -P_
infixl 30 _⊛P_

-- 内積
⟨_,_⟩ₛ : Pᶜ → Pᶜ → 𝕜
⟨ P₁ , P₂ ⟩ₛ = AlbertAlg.⟨ 𝔓ᶜ.X P₁ , 𝔓ᶜ.Y P₂ ⟩ⱼ𝕜

-- ================================================================
--  LAYER 2 : E₈ 構造体の定義と線形空間としての基本演算
-- ================================================================

-- E8 のレコード型定義
record E8 : Type where
  constructor mkE8
  field
    Φ : E7 ; P : Pᶜ ; Q : Pᶜ ; r : 𝕜 ; u : 𝕜 ; v : 𝕜

-- E8 用の演算子優先順位
infixl 20 _+E8_
infix  25 -E8_
infixl 30 _⊛E8_

-- E8 の加法
_+E8_ : E8 → E8 → E8
mkE8 Φ₁ P₁ Q₁ r₁ u₁ v₁ +E8 mkE8 Φ₂ P₂ Q₂ r₂ u₂ v₂ =
  mkE8 (Φ₁ +E7 Φ₂) (P₁ +P P₂) (Q₁ +P Q₂) (r₁ +𝕜 r₂) (u₁ +𝕜 u₂) (v₁ +𝕜 v₂)

-- E8 の符号反転
-E8_ : E8 → E8
-E8 (mkE8 Φ P Q r u v) = 
  mkE8 (-E7 Φ) (-P P) (-P Q) (-𝕜 r) (-𝕜 u) (-𝕜 v)

-- E8 のスカラー倍
_⊛E8_ : 𝕜 → E8 → E8
a ⊛E8 (mkE8 Φ P Q r u v) =
  mkE8 (a ⊛E7 Φ) (a ⊛P P) (a ⊛P Q) (a ·𝕜 r) (a ·𝕜 u) (a ·𝕜 v)

-- E8 の零元
E8-zero : E8
E8-zero = mkE8 E7-zero Pᶜ-zero Pᶜ-zero 𝕜-zero 𝕜-zero 𝕜-zero