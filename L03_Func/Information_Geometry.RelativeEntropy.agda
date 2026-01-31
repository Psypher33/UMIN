{-# OPTIONS --cubical --guardedness #-}
module 03_Translation_Functors.Information_Geometry.RelativeEntropy where
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Vec
open import Cubical.Data.FinData using (Fin; foldr; toℕ)
open import Agda.Builtin.Float
open import 03_Translation_Functors.MagnitudeTheory
-- 演算子の局所定義
private
  *+f* = primFloatPlus
  **f* = primFloatTimes
  *-f* = primFloatMinus
-- =========================================================================
-- [STAGE 1] 基本行列演算と零行列の定義
-- =========================================================================
module MatrixOps (n : ℕ) where
  
  zero-matrix : Matrix n
  zero-matrix = tabulate λ _ → tabulate λ _ → 0.0
  transpose : Matrix n → Matrix n
  transpose M = tabulate λ i → tabulate λ j → lookup i (lookup j M)
  matrix-trace : Matrix n → Float
  matrix-trace M =
    let diag = tabulate (λ i → lookup i (lookup i M))
    in foldr (λ _ x acc → x +f acc) 0.0 diag
  postulate
    matrix-mul : Matrix n → Matrix n → Matrix n
    matrix-sub : Matrix n → Matrix n → Matrix n
    matrix-exp : Matrix n → Matrix n
    
    -- 【修正の核心】性質の公理化
    sub-self-zero   : ∀ M → matrix-sub M M ≡ zero-matrix
    matrix-mul-zero : ∀ M → matrix-mul M zero-matrix ≡ zero-matrix
    trace-zero      : matrix-trace zero-matrix ≡ 0.0
-- =========================================================================
-- [STAGE 2] 密度行列と対数の性質 (修正版)
-- =========================================================================
record IsDensityMatrix {n : ℕ} (ρ : Matrix n) : Type where
  open MatrixOps n
  field
    hermitian  : ρ ≡ transpose ρ
    normalized : matrix-trace ρ ≡ 1.0
    postulate is-positive : Σ (Matrix n) (λ A → ρ ≡ matrix-mul A (transpose A))
record MatrixLogarithm {n : ℕ} (M : Matrix n) : Type where
  open MatrixOps n
  field
    log-val    : Matrix n
    -- 【修正】型を Matrix n から ≡ (Path) へ
    is-inverse : matrix-exp log-val ≡ M
-- =========================================================================
-- [STAGE 3] Entropic Action の定義と Q.E.D.
-- =========================================================================
module BianconiEmergence (n : ℕ) where
  open MatrixOps n
  entropic-action : (ρ σ : Matrix n)
                  → IsDensityMatrix ρ → IsDensityMatrix σ
                  → MatrixLogarithm ρ → MatrixLogarithm σ
                  → Float
  entropic-action ρ σ ρ-prop σ-prop ρ-log σ-log =
    let Lρ = MatrixLogarithm.log-val ρ-log
        Lσ = MatrixLogarithm.log-val σ-log
    in matrix-trace (matrix-mul ρ (matrix-sub Lρ Lσ))
  -- 【小さな勝利！】同一状態での作用ゼロ証明（Holeなし）
  entropic-action-zero : (ρ : Matrix n) (p : IsDensityMatrix ρ) (l : MatrixLogarithm ρ)
                       → entropic-action ρ ρ p p l l ≡ 0.0
  entropic-action-zero ρ p l =
    let Lρ = MatrixLogarithm.log-val l
        -- 1. Lρ - Lρ = 0
        step1 = sub-self-zero Lρ
        -- 2. ρ * 0 = 0
        step2 = cong (matrix-mul ρ) step1 ∙ matrix-mul-zero ρ
    in cong matrix-trace step2 ∙ trace-zero
  -- 【未来の勝利】非負性の宣言 (Kleinの不等式)
  -- 意味：宇宙の重力作用は常に「情報の不一致」から生じ、負にはならない
  postulate
    entropic-action-nonnegative : ∀ ρ σ p q lρ lσ → primFloatLess (entropic-action ρ σ p q lρ lσ) 0.0 ≡ false