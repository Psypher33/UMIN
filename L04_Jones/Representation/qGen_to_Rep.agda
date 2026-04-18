{-# OPTIONS --cubical --guardedness #-}

module UMIN.L04_Jones.Representation.qGen_to_Rep where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Group.Base using (Group₀)
open import UMIN.L04_Jones.Representation.FiberAut

-- 骨格：具体定義は [P]
postulate
  qGenerator    : Type₀
  SU2q          : Group₀
  LaurentModule : VectorSpace
  -- q-gen → 表現 → R行列への「降ろす経路」
  qGen-to-Rep   : qGenerator → Representation SU2q LaurentModule
