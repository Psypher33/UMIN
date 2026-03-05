{-# OPTIONS --cubical --guardedness #-}

module UMIN.L00_Core.Logic.FunctorComposition where

open import Cubical.Foundations.Prelude hiding (I)

open import UMIN.L00_Core.Logic.WeakMonoidalCategory
open import UMIN.L00_Core.Logic.MonoidalFunctor


-- ============================================================
-- Functor composition
-- ============================================================

module _
  {ℓobj ℓhom}
  (C : WeakMonoidalCategory {ℓobj} {ℓhom})
  where

  open WeakMonoidalCategory C
  open StrongMonoidalEndofunctor
  open CatIso

  ------------------------------------------------------------
  -- Object part
  ------------------------------------------------------------

  F₀-comp :
    (F G : StrongMonoidalEndofunctor C) →
    Obj → Obj
  F₀-comp F G X = F₀ F (F₀ G X)


  ------------------------------------------------------------
  -- Morphism part
  ------------------------------------------------------------

  F₁-comp :
    (F G : StrongMonoidalEndofunctor C) →
    ∀ {A B} →
    Hom A B →
    Hom (F₀-comp F G A) (F₀-comp F G B)

  F₁-comp F G f =
    F₁ F (F₁ G f)


  ------------------------------------------------------------
  -- Functor laws
  ------------------------------------------------------------

  postulate

    comp-F-id :
      ∀ (F G : StrongMonoidalEndofunctor C)
      {A : Obj} →
      F₁-comp F G (id {A})
      ≡
      id

    comp-F-comp :
      ∀ (F G : StrongMonoidalEndofunctor C)
      {A B D}
      (f : Hom B D)
      (g : Hom A B) →

      F₁-comp F G (f ∘ g)
      ≡
      F₁-comp F G f ∘ F₁-comp F G g


  ------------------------------------------------------------
  -- Monoidal structure μ
  ------------------------------------------------------------

  postulate

    μ-comp-to :
      (F G : StrongMonoidalEndofunctor C) →
      ∀ A B →

      Hom
        (F₀-comp F G (A ⊗ B))
        (F₀-comp F G A ⊗ F₀-comp F G B)

    μ-comp-from :
      (F G : StrongMonoidalEndofunctor C) →
      ∀ A B →

      Hom
        (F₀-comp F G A ⊗ F₀-comp F G B)
        (F₀-comp F G (A ⊗ B))

    μ-comp-inv-right :
      (F G : StrongMonoidalEndofunctor C) →
      ∀ A B →

      μ-comp-to F G A B
      ∘
      μ-comp-from F G A B
      ≡
      id

    μ-comp-inv-left :
      (F G : StrongMonoidalEndofunctor C) →
      ∀ A B →

      μ-comp-from F G A B
      ∘
      μ-comp-to F G A B
      ≡
      id


  ------------------------------------------------------------
  -- Unit structure
  ------------------------------------------------------------

  postulate

    ε-comp-to :
      (F G : StrongMonoidalEndofunctor C) →
      Hom (F₀-comp F G I) I

    ε-comp-from :
      (F G : StrongMonoidalEndofunctor C) →
      Hom I (F₀-comp F G I)

    ε-comp-inv-right :
      (F G : StrongMonoidalEndofunctor C) →
      ε-comp-to F G ∘ ε-comp-from F G ≡ id

    ε-comp-inv-left :
      (F G : StrongMonoidalEndofunctor C) →
      ε-comp-from F G ∘ ε-comp-to F G ≡ id


  ------------------------------------------------------------
  -- Final composed endofunctor
  ------------------------------------------------------------

  composeStrong :
    (F G : StrongMonoidalEndofunctor C) →
    StrongMonoidalEndofunctor C

  composeStrong F G .F₀ =
    F₀-comp F G

  composeStrong F G .F₁ =
    F₁-comp F G

  composeStrong F G .F-id =
    comp-F-id F G

  composeStrong F G .F-comp =
    comp-F-comp F G

  composeStrong F G .μ =
    λ A B →
      record
        { to = μ-comp-to F G A B
        ; from = μ-comp-from F G A B
        ; inv-right = μ-comp-inv-right F G A B
        ; inv-left = μ-comp-inv-left F G A B
        }

  composeStrong F G .ε_unit =
      record
        { to = ε-comp-to F G
        ; from = ε-comp-from F G
        ; inv-right = ε-comp-inv-right F G
        ; inv-left = ε-comp-inv-left F G
        }