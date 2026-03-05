{-# OPTIONS --cubical --safe --guardedness #-}

module UMIN.L00_Core.Logic.MonoidalFunctor where

open import Cubical.Foundations.Prelude hiding (I)
open import UMIN.L00_Core.Logic.WeakMonoidalCategory

-- ============================================================
-- 💡 圏論専用の Isomorphism (CatIso) の定義
-- ============================================================
record CatIso {ℓobj ℓhom} {C : WeakMonoidalCategory {ℓobj} {ℓhom}} (A B : WeakMonoidalCategory.Obj C) : Type (ℓ-max ℓobj ℓhom) where
  open WeakMonoidalCategory C
  field
    to       : Hom A B
    from     : Hom B A
    inv-right : to ∘ from ≡ id
    inv-left  : from ∘ to ≡ id

-- ============================================================
-- 1. Strong Monoidal Endofunctor (CatIso version)
-- ============================================================
record StrongMonoidalEndofunctor {ℓobj ℓhom} (C : WeakMonoidalCategory {ℓobj} {ℓhom}) : Type (ℓ-suc (ℓ-max ℓobj ℓhom)) where
  open WeakMonoidalCategory C

  field
    F₀ : Obj → Obj
    F₁ : ∀ {A B} → Hom A B → Hom (F₀ A) (F₀ B)

    F-id : ∀ {A : Obj} → F₁ (id {A}) ≡ id {A = F₀ A}
    F-comp : ∀ {A B D} (f : Hom B D) (g : Hom A B) → F₁ (f ∘ g) ≡ F₁ f ∘ F₁ g

    -- 💡 [修正] AgdaのIsoではなく、圏Cの内部における対象間のCatIsoを使用！
    μ : ∀ A B → CatIso {C = C} (F₀ (A ⊗ B)) (F₀ A ⊗ F₀ B)
    ε_unit : CatIso {C = C} (F₀ I) I

-- ============================================================
-- 2. Strong Monoidal AutoEquivalence
-- ============================================================
record StrongMonoidalAutoEquivalence {ℓobj ℓhom} (C : WeakMonoidalCategory {ℓobj} {ℓhom}) : Type (ℓ-suc (ℓ-max ℓobj ℓhom)) where
  open WeakMonoidalCategory C
  open StrongMonoidalEndofunctor

  field
    F   : StrongMonoidalEndofunctor C
    F⁻¹ : StrongMonoidalEndofunctor C

    η : ∀ A → Hom A (F₀ F⁻¹ (F₀ F A))
    ε : ∀ A → Hom (F₀ F (F₀ F⁻¹ A)) A

    triangle₁ : ∀ A → ε (F₀ F A) ∘ F₁ F (η A) ≡ id
    triangle₂ : ∀ A → F₁ F⁻¹ (ε A) ∘ η (F₀ F⁻¹ A) ≡ id