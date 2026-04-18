{-# OPTIONS --cubical --guardedness #-}

-- ================================================================
--  L03_Func/YBE/UMIN_YBE_Base.agda
--  R 行列・YBE の型定義（GroupRMatrix と Skeleton で共有）
-- ================================================================

module UMIN.L04_Jones.YBE.UMIN_YBE_Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

record RMatrix (V : Type) : Type where
  field
    R₁₂ R₁₃ R₂₃ : V × V × V → V × V × V

record YBEStructure (V : Type) : Type where
  field
    rm     : RMatrix V
    yb-eq  : (v : V × V × V) →
             RMatrix.R₁₂ rm (RMatrix.R₁₃ rm (RMatrix.R₂₃ rm v)) ≡
             RMatrix.R₂₃ rm (RMatrix.R₁₃ rm (RMatrix.R₁₂ rm v))
