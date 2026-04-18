{-# OPTIONS --cubical --guardedness #-}

module UMIN.L04_Jones.Representation.SU2q_Selection where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import UMIN.L04_Jones.YBE.UMIN_YBE_Base
open import UMIN.L04_Jones.YBE.SU2q_RMatrix

-- YBE 方程式（UMIN_YBE_Base の YBEStructure.yb-eq と同型）
satisfies-YBE : {V : Type} → RMatrix V → Type
satisfies-YBE {V} R = (v : V × V × V) →
  RMatrix.R₁₂ R (RMatrix.R₁₃ R (RMatrix.R₂₃ R v)) ≡
  RMatrix.R₂₃ R (RMatrix.R₁₃ R (RMatrix.R₁₂ R v))

-- 骨格 [H]：被覆との整合（具体定義は今後）
postulate
  compatible-with-covering : {V : Type} → RMatrix V → Type
  SU2q-standard-R          : RMatrix Basis3

-- なぜ SU(2)_q 型 R が選ばれるか（証明は [H]）
postulate
  SU2q-uniqueness :
    ∀ (R : RMatrix Basis3) →
    satisfies-YBE R →
    compatible-with-covering R →
    R ≡ SU2q-standard-R
