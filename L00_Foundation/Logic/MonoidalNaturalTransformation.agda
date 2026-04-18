{-# OPTIONS --cubical --safe --guardedness #-}

module UMIN.L00_Foundation.Logic.MonoidalNaturalTransformation where

open import Cubical.Foundations.Prelude hiding (I)
open import UMIN.L00_Foundation.Logic.WeakMonoidalCategory
open import UMIN.L00_Foundation.Logic.MonoidalFunctor

record MonoidalNaturalTransformation
  {ℓobj ℓhom}
  {C : WeakMonoidalCategory {ℓobj} {ℓhom}}
  (F G : StrongMonoidalEndofunctor C)
  : Type (ℓ-suc (ℓ-max ℓobj ℓhom)) where

  open WeakMonoidalCategory C
  open StrongMonoidalEndofunctor

  field
    η : ∀ A → Hom (F₀ F A) (F₀ G A)

    naturality :
      ∀ {A B} (f : Hom A B) →
      F₁ G f ∘ η A ≡ η B ∘ F₁ F f