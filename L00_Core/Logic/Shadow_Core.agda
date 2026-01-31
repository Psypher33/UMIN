{-# OPTIONS --cubical --safe --guardedness #-}

module UMIN.L00_Core.Logic.Shadow_Core where

open import Agda.Primitive using (Level; lzero; lsuc)
open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
-- ★ public を付けることで、このファイルを import した人も Sigma を使えるようになります
open import Cubical.Data.Sigma.Base public renaming (Σ to Sigma; _×_ to Times)
open import Cubical.Data.Empty as ⊥ public using (⊥; isProp⊥)

-- ================================================================
-- 【共通語彙】否定の定義
-- ================================================================
¬_ : ∀ {ℓ} → Type ℓ → Type ℓ
¬ A = A → ⊥

-- ================================================================
-- 【共通語彙】Shadow の定義
-- ================================================================
Shadow : {ℓ : Level} → (D F : Type ℓ) → (c : D → F) → Typeω
Shadow {ℓ} D F c =
  let
    Kernel = Sigma D (λ d₁ → 
               Sigma D (λ d₂ → 
                 Times (d₁ ≡ d₂ → ⊥) (c d₁ ≡ c d₂)))
  in
  ∀ {ℓ'} (P : Type ℓ') → isProp P → (Kernel → P) → P

-- ================================================================
-- 【共通語彙】No-Retraction の証明
-- ================================================================
Unified-Shadow-No-Retraction :
  {ℓ : Level} {D F : Type ℓ} (c : D → F)
  → Shadow D F c
  → ¬ (Sigma (F → D) (λ r → (λ x → r (c x)) ≡ (λ x → x)))
Unified-Shadow-No-Retraction {ℓ} {D} {F} c shadow (r , ret) =
  shadow ⊥ isProp⊥ (λ kernel-data → 
    let
      d₁      = fst kernel-data
      d₂      = fst (snd kernel-data)
      neq     = fst (snd (snd kernel-data))
      coll-eq = snd (snd (snd kernel-data))

      my-happly : {f g : D → D} → f ≡ g → (x : D) → f x ≡ g x
      my-happly p x = cong (λ h → h x) p

      eq₁ = my-happly ret d₁
      eq₂ = my-happly ret d₂
      same = cong r coll-eq
    in
      neq (sym eq₁ ∙ same ∙ eq₂)
  )