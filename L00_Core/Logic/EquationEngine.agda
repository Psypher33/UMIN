{-# OPTIONS --cubical --safe --guardedness #-}

module UMIN.L00_Core.Logic.EquationEngine where

open import Cubical.Foundations.Prelude

-- =======================================================================
-- UMIN Equation Engine
-- =======================================================================

infix  3 _∎⇒
infixr 2 _≡⟨_⟩⇒_
infix  1 begin⇒_

begin⇒_ : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ≡ y → x ≡ y
begin⇒_ p = p

_≡⟨_⟩⇒_ : ∀ {ℓ} {A : Type ℓ} (x : A) {y z : A}
         → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩⇒ q = p ∙ q

_∎⇒ : ∀ {ℓ} {A : Type ℓ} (x : A) → x ≡ x
_ ∎⇒ = refl