{-# OPTIONS --cubical --guardedness #-}

module UMIN.L01_Arithmetic.E8.E8_Layer2_Bracket where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _·_)

-- E7Interface から Lie積、作用、内積、スカラーなどの機能をインポート
open import UMIN.L01_Arithmetic.FTS.E7Interface
  using (E7; [_,_]₇; E7-act; _+E7_; -E7_; _×F_; B₇-definition; 𝕜; _+𝕜_; _·𝕜_; -𝕜_; ratEmbed; ℚ⁺; _//_)

-- 先ほど作成した Layer1 (土台) をインポートして E8 の構造を使う
open import UMIN.L01_Arithmetic.E8.E8_Layer1_Base
  using (E8; mkE8; Pᶜ; _+P_; -P_; _⊛P_; ⟨_,_⟩ₛ; _+E8_; E8-zero)

-- ================================================================
--  LAYER 2.5 : E₈ Lie積 [_,_]₈ (Abstract ブロックでフリーズ防止)
-- ================================================================

infix 35 [_,_]₈

abstract
  [_,_]₈ : E8 → E8 → E8
  [ R₁ , R₂ ]₈ = mkE8 Φ′ P′ Q′ r′ u′ v′
    where
      -- ローカル変数にすべて型を明示する（abstract 内での型推論ストップ・警告を防ぐため）
      Φ₁ : E7 ; Φ₁ = E8.Φ R₁
      Φ₂ : E7 ; Φ₂ = E8.Φ R₂
      P₁ : Pᶜ ; P₁ = E8.P R₁
      P₂ : Pᶜ ; P₂ = E8.P R₂
      Q₁ : Pᶜ ; Q₁ = E8.Q R₁
      Q₂ : Pᶜ ; Q₂ = E8.Q R₂
      r₁ : 𝕜  ; r₁ = E8.r R₁
      r₂ : 𝕜  ; r₂ = E8.r R₂
      u₁ : 𝕜  ; u₁ = E8.u R₁
      u₂ : 𝕜  ; u₂ = E8.u R₂
      v₁ : 𝕜  ; v₁ = E8.v R₁
      v₂ : 𝕜  ; v₂ = E8.v R₂

      Φ′ : E7
      Φ′ = ([ Φ₁ , Φ₂ ]₇) +E7 (P₁ ×F Q₂) +E7 (-E7 (P₂ ×F Q₁))

      P′ : Pᶜ
      P′ = (E7-act Φ₁ P₂) +P (-P (E7-act Φ₂ P₁)) +P (r₁ ⊛P P₂) +P (-P (r₂ ⊛P P₁)) +P (u₁ ⊛P Q₂) +P (-P (u₂ ⊛P Q₁))

      Q′ : Pᶜ
      Q′ = (E7-act Φ₁ Q₂) +P (-P (E7-act Φ₂ Q₁)) +P (-P (r₁ ⊛P Q₂)) +P (r₂ ⊛P Q₁) +P (v₁ ⊛P P₂) +P (-P (v₂ ⊛P P₁))

      r′ : 𝕜
      r′ = (-𝕜 ⟨ P₁ , Q₂ ⟩ₛ) +𝕜 ⟨ P₂ , Q₁ ⟩ₛ +𝕜 (u₁ ·𝕜 v₂) +𝕜 (-𝕜 (u₂ ·𝕜 v₁))

      u′ : 𝕜
      u′ = (-𝕜 ⟨ P₁ , P₂ ⟩ₛ) +𝕜 (ratEmbed (2 // 1) (r₁ ·𝕜 u₂)) +𝕜 (-𝕜 (ratEmbed (2 // 1) (r₂ ·𝕜 u₁)))

      v′ : 𝕜
      v′ = (-𝕜 ⟨ Q₁ , Q₂ ⟩ₛ) +𝕜 (-𝕜 (ratEmbed (2 // 1) (r₁ ·𝕜 v₂))) +𝕜 (ratEmbed (2 // 1) (r₂ ·𝕜 v₁))

-- ================================================================
--  LAYER 3 : Killing形式 B₈ (Abstract ブロック)
-- ================================================================

record KillingCoeffs : Type where
  constructor mkCoeffs
  field k₁ k₂ k₃ : ℚ⁺

miyashita-coeffs : KillingCoeffs
miyashita-coeffs = mkCoeffs (5 // 3) (15 // 1) (120 // 1)

abstract
  B₈ : KillingCoeffs → E8 → E8 → 𝕜
  B₈ κ R₁ R₂ =
      ratEmbed (KillingCoeffs.k₁ κ) (B₇-definition (E8.Φ R₁) (E8.Φ R₂))
      +𝕜 ratEmbed (KillingCoeffs.k₂ κ) (⟨ E8.Q R₁ , E8.P R₂ ⟩ₛ)
      +𝕜 (-𝕜 (ratEmbed (KillingCoeffs.k₂ κ) (⟨ E8.P R₁ , E8.Q R₂ ⟩ₛ)))
      +𝕜 ratEmbed (KillingCoeffs.k₃ κ) (E8.r R₁ ·𝕜 E8.r R₂)

-- ================================================================
--  Lie環としてのヤコビ恒等式の宣言
-- ================================================================

postulate
  E8-is-LieAlgebra : (X Y Z : E8) → 
    (([ X , [ Y , Z ]₈ ]₈) +E8 ([ Y , [ Z , X ]₈ ]₈) +E8 ([ Z , [ X , Y ]₈ ]₈)) ≡ E8-zero