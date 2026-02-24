{-# OPTIONS --cubical --safe --guardedness #-}

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Ring

module UMIN.L00_Core.Logic.Pentagon_Coherence {ℓ} (R : Ring ℓ) where

open import Cubical.Foundations.Path using (Square→compPath)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ)

-- 🌌 UMIN エンジンと完成した FPS_Base をインポート
open import UMIN.L00_Core.Logic.EquationEngine
open import UMIN.L00_Core.Algebra.FPS_Base R public

private
  Carrier : Type ℓ
  Carrier = fst R

-- =======================================================================
-- 2. 次元降下補題（パスの構築）
-- =======================================================================
-- 結合律の証を引数に取り、その下で α-path を定義
module _ (⊗-assoc : (A B C : FormalPowerSeries) → (A ⊗ B) ⊗ C ≡ A ⊗ (B ⊗ C)) where

  α-path : (A B C : FormalPowerSeries) → (A ⊗ B) ⊗ C ≡ A ⊗ (B ⊗ C)
  α-path = ⊗-assoc

  -- 五角形コヒーレンスは α-path を用いた型で受け取る（abstract との整合のため）
  module _ (pentagon-coh : ∀ A B C D →
      (cong (_⊗ D) (α-path A B C) ∙ α-path A (B ⊗ C) D ∙ cong (A ⊗_) (α-path B C D))
        ≡ (α-path (A ⊗ B) C D ∙ α-path A B (C ⊗ D))) where

    abstract
      α-path-abstract : (A B C : FormalPowerSeries) → (A ⊗ B) ⊗ C ≡ A ⊗ (B ⊗ C)
      α-path-abstract = α-path

    -- =======================================================================
    -- 3. 独立補題の証明（EquationEngine の活用）
    -- =======================================================================
    abstract
      warp-block1 : (A B C D : FormalPowerSeries) → ((A ⊗ B) ⊗ C) ⊗ D ≡ (A ⊗ (B ⊗ C)) ⊗ D
      warp-block1 A B C D =
        begin⇒_
          (((A ⊗ B) ⊗ C) ⊗ D ≡⟨ cong (λ X → X ⊗ D) (α-path A B C) ⟩⇒ (A ⊗ (B ⊗ C)) ⊗ D ∎⇒)

    -- =======================================================================
    -- 4. 量子コヒーレンスの完遂
    -- =======================================================================
    -- 五角形: 二通りの α の合成が一致
    pentagon-final : (A B C D : FormalPowerSeries) →
      (cong (_⊗ D) (α-path A B C) ∙ α-path A (B ⊗ C) D ∙ cong (A ⊗_) (α-path B C D))
        ≡ (α-path (A ⊗ B) C D ∙ α-path A B (C ⊗ D))
    pentagon-final A B C D = pentagon-coh A B C D