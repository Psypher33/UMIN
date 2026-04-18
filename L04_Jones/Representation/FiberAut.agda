{-# OPTIONS --cubical --guardedness #-}

module UMIN.L04_Jones.Representation.FiberAut where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩; str)
open import Cubical.Algebra.Group.Base using (Group₀; GroupStr)

-- 具体モデルは未置き（骨格）
postulate
  VectorSpace : Type₁
  GL          : VectorSpace → Type₀
  id-GL       : {V : VectorSpace} → GL V
  _∘GL_       : {V : VectorSpace} → GL V → GL V → GL V

-- Aut(Fiber) → GL(V) への表現
record Representation (G : Group₀) (V : VectorSpace) : Type₁ where
  open GroupStr (str G)
  field
    ρ      : ⟨ G ⟩ → GL V
    ρ-id   : ρ 1g ≡ id-GL
    ρ-comp : ∀ g h → ρ (g · h) ≡ ρ g ∘GL ρ h
