{-# OPTIONS --cubical --guardedness #-}

module UMIN.L03_Dynamic.Pentagon.PentagonAxiom_Operad where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path

-- §1. ⊗ の必須構造 (v3.0 確定版)
postulate
  Obj : Type₀
  _⊗_ : Obj → Obj → Obj
  map⊗ : {a a' b b' : Obj} → a ≡ a' → b ≡ b' → (a ⊗ b) ≡ (a' ⊗ b')
  map⊗-refl : (a b : Obj) → map⊗ {a}{a}{b}{b} refl refl ≡ refl
  -- 相棒発見：これが無いと詰む核心の interchange
  ⊗-∙ : {a₁ a₂ a₃ b₁ b₂ b₃ : Obj} → (p : a₁ ≡ a₂)(p' : a₂ ≡ a₃)
        → (q : b₁ ≡ b₂)(q' : b₂ ≡ b₃)
        → map⊗ (p ∙ p') (q ∙ q') ≡ map⊗ p q ∙ map⊗ p' q'
  α : (a b c : Obj) → (a ⊗ b) ⊗ c ≡ a ⊗ (b ⊗ c)

-- §2. 共有辺 m の設計 (最重要タスク)
-- 型: P1 ≡ P4 (5頂点図より導出)
m-type : (A B C D : Obj) → Type₀
m-type A B C D = (A ⊗ B) ⊗ (C ⊗ D) ≡ A ⊗ ((B ⊗ C) ⊗ D)

-- §3. sq₁・sq₂ の型確定 (Phase 1: postulate宣言)
postulate
  sq₁ : (A B C D : Obj) → Square 
          (α (A ⊗ B) C D)                 -- e01
          (map⊗ (α A B C) refl ∙ α A (B ⊗ C) D) -- e03 ∙ e34
          refl                             -- 左辺
          (α A B (C ⊗ D) ∙ map⊗ refl (sym (α B C D))) -- m：上右 → 下右（m-type）

-- ※ 実際には Eva の pentagon-type に合わせ sq₁・sq₂ を再定義
pentagon-type : (A B C D : Obj) → Type₀
pentagon-type A B C D = Square 
  (α (A ⊗ B) C D ∙ α A B (C ⊗ D))                      -- 上辺：e01 ∙ e12
  ((map⊗ (α A B C) refl ∙ α A (B ⊗ C) D) ∙ map⊗ refl (α B C D)) -- 下辺（∙₂ と括弧一致：infixr _∙_ との差を避ける）
  refl -- 左辺
  refl -- 右辺

postulate
  sq₁-v3 : (A B C D : Obj) → Square (α (A ⊗ B) C D) (map⊗ (α A B C) refl ∙ α A (B ⊗ C) D) refl (α A B (C ⊗ D) ∙ map⊗ refl (sym (α B C D)))
  sq₂-v3 : (A B C D : Obj) → Square (α A B (C ⊗ D)) (map⊗ refl (α B C D)) (α A B (C ⊗ D) ∙ map⊗ refl (sym (α B C D))) refl

-- §4. Pentagon Coherence の器 (Phase 1 完了)[cite: 5]
pentagon-coherence : (A B C D : Obj) → pentagon-type A B C D
pentagon-coherence A B C D = sq₁-v3 A B C D ∙₂ sq₂-v3 A B C D