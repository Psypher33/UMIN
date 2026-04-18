{-# OPTIONS --cubical --safe --guardedness #-}

module UMIN.L00_Foundation.Logic.WeakMonoidalCategory where

open import Cubical.Foundations.Prelude hiding (I)
open import Cubical.Foundations.Function hiding (_∘_)

record WeakMonoidalCategory {ℓobj ℓhom : Level}
  : Type (ℓ-suc (ℓ-max ℓobj ℓhom)) where

  field
    ------------------------------------------------------------------
    -- 1. Category structure
    ------------------------------------------------------------------

    Obj : Type ℓobj
    Hom : Obj → Obj → Type ℓhom

    id  : ∀ {A} → Hom A A
    _∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C

    assoc :
      ∀ {A B C D}
      (f : Hom C D)
      (g : Hom B C)
      (h : Hom A B) →
      f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h

    id-left :
      ∀ {A B} (f : Hom A B) →
      id ∘ f ≡ f

    id-right :
      ∀ {A B} (f : Hom A B) →
      f ∘ id ≡ f

    ------------------------------------------------------------------
    -- 2. Monoidal structure
    ------------------------------------------------------------------

    I : Obj
    _⊗_ : Obj → Obj → Obj

    tensorHom :
      ∀ {A B C D}
      → Hom A C
      → Hom B D
      → Hom (A ⊗ B) (C ⊗ D)

    tensor-id :
      ∀ {A B : Obj} →
      tensorHom {A}{B}{A}{B} id id ≡ id {A = A ⊗ B}

    tensor-comp :
      ∀ {A B C D E F}
      (f₁ : Hom A B)
      (f₂ : Hom B C)
      (g₁ : Hom D E)
      (g₂ : Hom E F) →
      tensorHom (f₂ ∘ f₁) (g₂ ∘ g₁)
      ≡
      (tensorHom f₂ g₂) ∘ (tensorHom f₁ g₁)

    ------------------------------------------------------------------
    -- Associator
    ------------------------------------------------------------------

    Φ :
      ∀ A B C →
      Hom ((A ⊗ B) ⊗ C)
          (A ⊗ (B ⊗ C))

    Φ⁻¹ :
      ∀ A B C →
      Hom (A ⊗ (B ⊗ C))
          ((A ⊗ B) ⊗ C)

    Φ-inv-right :
      ∀ A B C →
      Φ A B C ∘ Φ⁻¹ A B C ≡ id

    Φ-inv-left :
      ∀ A B C →
      Φ⁻¹ A B C ∘ Φ A B C ≡ id

    Φ-natural :
      ∀ {A A' B B' C C'}
      (f : Hom A A')
      (g : Hom B B')
      (h : Hom C C') →

      Φ A' B' C'
      ∘ tensorHom (tensorHom f g) h

      ≡

      tensorHom f (tensorHom g h)
      ∘ Φ A B C

    pentagon :
      ∀ A B C D →
      let
        X₀ = (((A ⊗ B) ⊗ C) ⊗ D)
        X₁ = ((A ⊗ (B ⊗ C)) ⊗ D)
        X₂ = (A ⊗ ((B ⊗ C) ⊗ D))
        X₃ = (A ⊗ (B ⊗ (C ⊗ D)))

        p1 = tensorHom (Φ A B C) id
        p2 = Φ A (B ⊗ C) D
        p3 = tensorHom id (Φ B C D)

        path1 = p3 ∘ (p2 ∘ p1)

        q1 = Φ (A ⊗ B) C D
        q2 = Φ A B (C ⊗ D)

        path2 = q2 ∘ q1
      in
        path1 ≡ path2