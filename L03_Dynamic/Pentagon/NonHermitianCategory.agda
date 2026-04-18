{-# OPTIONS --cubical --safe --guardedness #-}

module UMIN.L03_Dynamic.Pentagon.NonHermitianCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit using (Unit; tt)

open import UMIN.L00_Foundation.Logic.WeakMonoidalCategory
open import UMIN.L03_Dynamic.TremblingCore.NonHermitianObject

-- ============================================================
-- 非エルミートオブジェクトの弱モノイド圏スケルトン
--   （まずは圏構造のみを与える）
-- ============================================================

NonHermitianCat :
  WeakMonoidalCategory
    {ℓobj = ℓ-suc (ℓ-suc ℓ-zero)}
    {ℓhom = ℓ-zero}
NonHermitianCat = record
  { Obj = NonHermitianObject
  ; Hom = λ _ _ → Unit

  ; id  = tt
  ; _∘_ = λ f g → tt

  ; assoc    = λ {A} {B} {C} {D} f g h → refl
  ; id-left  = λ {A} {B} f → refl
  ; id-right = λ {A} {B} f → refl

  ; I    = unitNH
  ; _⊗_  = λ A B → A

  ; tensorHom  = λ {A}{B}{C}{D} f g → tt
  ; tensor-id  = λ {A}{B} → refl
  ; tensor-comp = λ {A}{B}{C}{D}{E}{F} f₁ f₂ g₁ g₂ → refl

  ; Φ           = λ A B C → tt
  ; Φ⁻¹         = λ A B C → tt
  ; Φ-inv-right = λ A B C → refl
  ; Φ-inv-left  = λ A B C → refl
  ; Φ-natural   = λ {A}{A'}{B}{B'}{C}{C'} f g h → refl
  ; pentagon    = λ A B C D → refl
  }

