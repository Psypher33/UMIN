{-# OPTIONS --cubical --safe --guardedness #-}

module UMIN.L03_Dynamic.Pentagon.BraidedMonoidalCategory where

open import Cubical.Foundations.Prelude hiding (I)
open import UMIN.L00_Foundation.Logic.WeakMonoidalCategory

-- ============================================================
-- Braided Monoidal Category
-- ============================================================

record BraidedMonoidalCategory
  {ℓobj ℓhom}
  (C : WeakMonoidalCategory {ℓobj} {ℓhom})
  : Type (ℓ-suc (ℓ-max ℓobj ℓhom)) where

  open WeakMonoidalCategory C

  field

    ------------------------------------------------------------
    -- Braiding
    ------------------------------------------------------------

    β :
      ∀ A B →
      Hom (A ⊗ B)
          (B ⊗ A)

    β⁻¹ :
      ∀ A B →
      Hom (B ⊗ A)
          (A ⊗ B)

    β-inv-right :
      ∀ A B →
      β A B ∘ β⁻¹ A B ≡ id

    β-inv-left :
      ∀ A B →
      β⁻¹ A B ∘ β A B ≡ id


    ------------------------------------------------------------
    -- Naturality
    ------------------------------------------------------------

    β-natural :

      ∀ {A A' B B'}
      (f : Hom A A')
      (g : Hom B B') →

      tensorHom g f
      ∘
      β A B

      ≡

      β A' B'
      ∘
      tensorHom f g


    ------------------------------------------------------------
    -- Hexagon identities
    ------------------------------------------------------------

    hexagon₁ :

      ∀ A B C →

      let

        left =
          (Φ B C A ∘ β A (B ⊗ C)) ∘ Φ A B C

        right =
          (tensorHom id (β A C) ∘ Φ B A C) ∘ tensorHom (β A B) id

      in
        left ≡ right


    hexagon₂ :

      ∀ A B C →

      let

        left =
          (Φ⁻¹ C A B ∘ β (A ⊗ B) C) ∘ Φ⁻¹ A B C

        right =
          (tensorHom (β A C) id ∘ Φ⁻¹ A C B) ∘ tensorHom id (β B C)

      in
        left ≡ right