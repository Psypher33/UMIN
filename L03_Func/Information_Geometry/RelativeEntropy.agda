{-# OPTIONS --cubical --guardedness #-}
module UMIN.L03_Func.Information_Geometry.RelativeEntropy where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Vec using (Vec; lookup; foldr; _∷_; [])
open import Cubical.Data.FinData using (Fin; toℕ)
-- ★ここで Bool 型と false をインポートします
open import Cubical.Data.Bool using (Bool; false)
open import Agda.Builtin.Float

-- 演算子の定義
_+f_ = primFloatPlus
_*f_ = primFloatTimes
_-f_ = primFloatMinus

-- =========================================================================
-- [STAGE 0] 自前 tabulate (依存関係の回避)
-- =========================================================================
my-tabulate : {A : Type} {n : ℕ} → (Fin n → A) → Vec A n
my-tabulate {n = zero} f = []
my-tabulate {n = suc n} f = f ( Fin.zero ) ∷ my-tabulate (λ x → f (Fin.suc x))

-- =========================================================================
-- [STAGE 1] 行列演算の基本定義
-- =========================================================================
module MatrixOps (n : ℕ) where
  
  Matrix : Type
  Matrix = Vec (Vec Float n) n

  zero-matrix : Matrix
  zero-matrix = my-tabulate λ _ → my-tabulate λ _ → 0.0

  transpose : Matrix → Matrix
  transpose M = my-tabulate λ i → my-tabulate λ j → lookup i (lookup j M)

  matrix-trace : Matrix → Float
  matrix-trace M =
    let diag = my-tabulate (λ i → lookup i (lookup i M))
    in foldr (λ x acc → x +f acc) 0.0 diag

  postulate
    matrix-mul : Matrix → Matrix → Matrix
    matrix-sub : Matrix → Matrix → Matrix
    matrix-exp : Matrix → Matrix
    
    sub-self-zero   : ∀ M → matrix-sub M M ≡ zero-matrix
    matrix-mul-zero : ∀ M → matrix-mul M zero-matrix ≡ zero-matrix
    trace-zero      : matrix-trace zero-matrix ≡ 0.0

-- =========================================================================
-- [STAGE 2] 密度行列と対数の性質
-- =========================================================================

record IsDensityMatrix {n : ℕ} (ρ : MatrixOps.Matrix n) : Type where
  open MatrixOps n
  field
    hermitian   : ρ ≡ transpose ρ
    normalized  : matrix-trace ρ ≡ 1.0
    is-positive : Σ Matrix (λ A → ρ ≡ matrix-mul A (transpose A))

record MatrixLogarithm {n : ℕ} (M : MatrixOps.Matrix n) : Type where
  open MatrixOps n
  field
    log-val    : Matrix
    is-inverse : matrix-exp log-val ≡ M

-- =========================================================================
-- [STAGE 3] Entropic Action の定義
-- =========================================================================
module BianconiEmergence (n : ℕ) where
  open MatrixOps n
  
  entropic-action : (ρ σ : Matrix)
                  → IsDensityMatrix ρ → IsDensityMatrix σ
                  → MatrixLogarithm ρ → MatrixLogarithm σ
                  → Float
  entropic-action ρ σ ρ-prop σ-prop ρ-log σ-log =
    let Lρ = MatrixLogarithm.log-val ρ-log
        Lσ = MatrixLogarithm.log-val σ-log
    in matrix-trace (matrix-mul ρ (matrix-sub Lρ Lσ))

  entropic-action-zero : (ρ : Matrix) (p : IsDensityMatrix ρ) (l : MatrixLogarithm ρ)
                       → entropic-action ρ ρ p p l l ≡ 0.0
  entropic-action-zero ρ p l =
    let Lρ = MatrixLogarithm.log-val l
        step1 = sub-self-zero Lρ
        step2 = cong (matrix-mul ρ) step1 ∙ matrix-mul-zero ρ
    in cong matrix-trace step2 ∙ trace-zero

  -- これで false が認識されます！
  postulate
    entropic-action-nonnegative : ∀ ρ σ p q lρ lσ 
                                → primFloatLess (entropic-action ρ σ p q lρ lσ) 0.0 ≡ false