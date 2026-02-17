{-# OPTIONS --cubical --safe --guardedness #-}

module UMIN.L00_Core.Logic.WeakMonoidalCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function hiding (_∘_)

record WeakMonoidalCategory {ℓobj ℓhom : Level}
  : Type (ℓ-suc (ℓ-max ℓobj ℓhom)) where

  field
    ----------------------------------------------------------------------
    -- 1. 圏構造
    ----------------------------------------------------------------------

    Obj : Type ℓobj
    Hom : Obj → Obj → Type ℓhom

    id  : ∀ {A} → Hom A A
    _∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C

-- 以下、そのままのコードが続きます...

    -- 圏の公理
    assoc :
      ∀ {A B C D}
      (f : Hom C D)
      (g : Hom B C)
      (h : Hom A B) →
      f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h

    id-left :
      ∀ {A B}
      (f : Hom A B) →
      id ∘ f ≡ f

    id-right :
      ∀ {A B}
      (f : Hom A B) →
      f ∘ id ≡ f

    ----------------------------------------------------------------------
    -- 2. テンソル構造
    ----------------------------------------------------------------------

    _⊗_ : Obj → Obj → Obj

    tensorHom :
      ∀ {A B C D}
      → Hom A C
      → Hom B D
      → Hom (A ⊗ B) (C ⊗ D)

    ----------------------------------------------------------------------
    -- tensor の関手性
    ----------------------------------------------------------------------

    tensor-id :
      ∀ {A B} →
      tensorHom (id {A = A}) (id {A = B})
      ≡ id

    tensor-comp :
      ∀ {A B C D E F}
      (f₁ : Hom A B)
      (f₂ : Hom B C)
      (g₁ : Hom D E)
      (g₂ : Hom E F) →

      tensorHom (f₂ ∘ f₁) (g₂ ∘ g₁)
      ≡
      (tensorHom f₂ g₂) ∘ (tensorHom f₁ g₁)

    ----------------------------------------------------------------------
    -- 3. アソシエータ（自然同型）
    ----------------------------------------------------------------------

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

    ----------------------------------------------------------------------
    -- Φ の自然性
    ----------------------------------------------------------------------

    Φ-natural :
      ∀ {A A' B B' C C'}
      (f : Hom A A')
      (g : Hom B B')
      (h : Hom C C') →

      let
        left :
          Hom (((A ⊗ B) ⊗ C))
              (A' ⊗ (B' ⊗ C'))
        left =
          Φ A' B' C'
          ∘ (tensorHom (tensorHom f g) h)

        right :
          Hom (((A ⊗ B) ⊗ C))
              (A' ⊗ (B' ⊗ C'))
        right =
          (tensorHom f (tensorHom g h))
          ∘ Φ A B C
      in
        left ≡ right

    ----------------------------------------------------------------------
    -- 4. 五角形関係式（Pentagon）
    ----------------------------------------------------------------------

    pentagon :
      ∀ A B C D →

      let
        X₀ = (((A ⊗ B) ⊗ C) ⊗ D)
        X₁ = ((A ⊗ (B ⊗ C)) ⊗ D)
        X₂ = (A ⊗ ((B ⊗ C) ⊗ D))
        X₃ = (A ⊗ (B ⊗ (C ⊗ D)))

        -- 上ルート
        p1-1 : Hom X₀ X₁
        p1-1 = tensorHom (Φ A B C) id

        p1-2 : Hom X₁ X₂
        p1-2 = Φ A (B ⊗ C) D

        p1-3 : Hom X₂ X₃
        p1-3 = tensorHom id (Φ B C D)

        path1 : Hom X₀ X₃
        path1 = p1-3 ∘ (p1-2 ∘ p1-1)

        -- 下ルート
        Y₁ = ((A ⊗ B) ⊗ (C ⊗ D))

        p2-1 : Hom X₀ Y₁
        p2-1 = Φ (A ⊗ B) C D

        p2-2 : Hom Y₁ X₃
        p2-2 = Φ A B (C ⊗ D)

        path2 : Hom X₀ X₃
        path2 = p2-2 ∘ p2-1

      in
        path1 ≡ path2
