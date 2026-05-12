{-# OPTIONS --cubical --safe --guardedness #-}

module UMIN.L00_Foundation.HomotopyTheory.Pointed where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

--------------------------------------------------
-- 1. Pointed type と Pointed map（スケルトン）
--------------------------------------------------

record Pointed : Type₁ where
  field
    Space : Type₀
    pt    : Space

record PointedMap (A B : Pointed) : Type₁ where
  field
    f       : Pointed.Space A → Pointed.Space B
    pt-pres : f (Pointed.pt A) ≡ Pointed.pt B

--------------------------------------------------
-- 2. 恒等写像
--------------------------------------------------

id-pointed : (A : Pointed) → PointedMap A A
id-pointed A = record
  { f       = λ x → x
  ; pt-pres = refl
  }

--------------------------------------------------
-- 3. 合成
--------------------------------------------------

comp-pointed : {A B C : Pointed}
  → PointedMap B C → PointedMap A B → PointedMap A C
comp-pointed {A} {B} {C} G F = record
  { f       = λ x → PointedMap.f G (PointedMap.f F x)
  ; pt-pres =
      -- G(F(pt A)) ≡ G(pt B) ≡ pt C
      cong (PointedMap.f G) (PointedMap.pt-pres F)
      ∙ PointedMap.pt-pres G
  }

--------------------------------------------------
-- 4. pt-pres の合成則
--------------------------------------------------

comp-pt-pres : {A B C : Pointed}
  (G : PointedMap B C) (F : PointedMap A B)
  → PointedMap.f (comp-pointed G F) (Pointed.pt A)
    ≡ Pointed.pt C
comp-pt-pres G F = PointedMap.pt-pres (comp-pointed G F)
