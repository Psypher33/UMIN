{-# OPTIONS --cubical --guardedness #-}

module UMIN.L03_Func.NumericalExperiment.PauliStates where

open import Cubical.Foundations.Prelude
open import Agda.Builtin.Float
open import Cubical.Data.Nat
open import Cubical.Data.Vec
open import Cubical.Data.FinData using (Fin; zero; suc)
open import Cubical.Data.Bool using (if_then_else_; Bool; false; true)
open import UMIN.L03_Func.Information_Geometry.RelativeEntropy

-- =========================================================================
-- [STAGE 1] n=2 行列演算の最終洗練
-- =========================================================================

module MatrixOps2 where
  open MatrixOps 2 public

  -- 曖昧さを排除するため、型を明示的に指定したインデックスを定義
  idx0 : Fin 2
  idx0 = zero

  idx1 : Fin 2
  idx1 = suc zero

  matrix-mul-2 : Matrix → Matrix → Matrix
  matrix-mul-2 A B = 
    let 
      -- lookup に渡すインデックスを明示的に idx0 / idx1 に固定
      a00 = lookup idx0 (lookup idx0 A); a01 = lookup idx1 (lookup idx0 A)
      a10 = lookup idx0 (lookup idx1 A); a11 = lookup idx1 (lookup idx1 A)
      b00 = lookup idx0 (lookup idx0 B); b01 = lookup idx1 (lookup idx0 B)
      b10 = lookup idx0 (lookup idx1 B); b11 = lookup idx1 (lookup idx1 B)
    in ( ( (a00 *f b00) +f (a01 *f b10) ) ∷ ( (a00 *f b01) +f (a01 *f b11) ) ∷ [] )
     ∷ ( ( (a10 *f b00) +f (a11 *f b10) ) ∷ ( (a10 *f b01) +f (a11 *f b11) ) ∷ [] ) ∷ []

  matrix-sub-2 : Matrix → Matrix → Matrix
  matrix-sub-2 A B = my-tabulate λ i → my-tabulate λ j → 
    lookup i (lookup j A) -f lookup i (lookup j B)

  matrix-log-2-diag : Matrix → Matrix
  matrix-log-2-diag M = my-tabulate λ (i : Fin 2) → my-tabulate λ (j : Fin 2) → 
    -- if_then_else_ の条件式の型も明示的に扱う
    let i-eq-j = Cubical.Data.FinData._==_ i j in
    if i-eq-j then 
      (let val = lookup i (lookup i M)
       in if primFloatLess val 1.0e-15 then 0.0 else primFloatLog val)
    else 0.0

-- =========================================================================
-- [STAGE 2] 宇宙の最小エントロピー実験 (ここが抜けていました！)
-- =========================================================================

module PauliExperiment where
  open MatrixOps2
  open BianconiEmergence 2

  rho-up : Matrix
  rho-up = (1.0 ∷ 0.0 ∷ []) ∷ (0.0 ∷ 0.0 ∷ []) ∷ []

  sigma-mixed : Matrix
  sigma-mixed = (0.5 ∷ 0.0 ∷ []) ∷ (0.0 ∷ 0.5 ∷ []) ∷ []

  postulate
    rho-is-state   : IsDensityMatrix rho-up
    sigma-is-state : IsDensityMatrix sigma-mixed
    rho-log-rec    : MatrixLogarithm rho-up
    sigma-log-rec  : MatrixLogarithm sigma-mixed

  calculate-relative-entropy : Float
  calculate-relative-entropy = 
    let 
      Lρ = MatrixLogarithm.log-val rho-log-rec
      Lσ = MatrixLogarithm.log-val sigma-log-rec
      diff = matrix-sub-2 Lρ Lσ
      prod = matrix-mul-2 rho-up diff
    in matrix-trace prod

-- =========================================================================
-- [STAGE 3] 外部公開用エイリアス
-- =========================================================================

LN2-Value : Float
LN2-Value = PauliExperiment.calculate-relative-entropy