{-# OPTIONS --cubical --guardedness --safe #-}

module UMIN.L01_Arithmetic.AlgebraicStructures.LieG2 where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)

open import UMIN.L01_Arithmetic.AlgebraicStructures.CompositionAlgebras as CA
open import UMIN.L01_Arithmetic.AlgebraicStructures.LieAlgebra as LA

-- ================================================================
-- LieG2 Layer: G₂ の導分と E₈ への埋め込みの「型レベル仕様」
-- （全てパラメータ化し、postulate を排除）
-- ================================================================

record LieG2Context : Type₁ where
  field
    ctx : LA.G2AlgebraContext

-- ================================================================
-- PART 1: Schafer Operators（G₂ の導分生成子）
-- ================================================================

module Schafer (C : LieG2Context) where
  open LieG2Context C
  open LA.G2AlgebraContext ctx
  module L = LA.G2-Layer ctx
  -- A（代数本体）と、その演算をローカル名で束縛しておく
  A₀ : Type
  A₀ = LA.G2AlgebraContext.A ctx

  Alg₀ : CA.CompositionAlgebra (LA.G2AlgebraContext.𝔽 ctx) A₀
  Alg₀ = LA.G2AlgebraContext.Alg ctx

  mulA : A₀ → A₀ → A₀
  mulA = CA.CompositionAlgebra.mul Alg₀

  _+A₀_ : A₀ → A₀ → A₀
  _+A₀_ = CA.AdditiveGroup._+A_ (CA.CompositionAlgebra.addGroup Alg₀)

  -A₀_ : A₀ → A₀
  -A₀_ = CA.AdditiveGroup.-A_ (CA.CompositionAlgebra.addGroup Alg₀)

  L R : A₀ → A₀ → A₀
  L a x = mulA a x
  R a x = mulA x a

  op-bracket : (A₀ → A₀) → (A₀ → A₀) → (A₀ → A₀)
  op-bracket F G x = (F (G x)) +A₀ (-A₀ (G (F x)))

  D-gen : A₀ → A₀ → A₀ → A₀
  D-gen a b x = ((op-bracket (L a) (L b) x) +A₀ (op-bracket (L a) (R b) x)) +A₀ (op-bracket (R a) (R b) x)

-- ================================================================
-- PART 2: Triality（型レベルのインターフェース）
-- ================================================================

record Triality (C : LieG2Context) : Type₁ where
  open LieG2Context C
  open LA.G2AlgebraContext ctx
  field
    V  S⁺ S⁻ : Type
    t : V → S⁺ → S⁻ → CA.CompAlgScalarField.ℚ (LA.G2AlgebraContext.𝔽 ctx)

-- ================================================================
-- PART 3: E₈ Lie Algebra と G₂ 導分の橋渡し
-- ================================================================

record E8LieAlgebra (C : LieG2Context) : Type₁ where
  open LieG2Context C
  open LA.G2AlgebraContext ctx
  module L = LA.G2-Layer ctx
  open L

  field
    -- E₈ 本体
    e₈     : Type
    ε-zero : e₈
    _+E8_  : e₈ → e₈ → e₈

    dim-e₈ : ℕ
    bracket-e₈ : e₈ → e₈ → e₈

    -- Jacobi 身分
    jacobi : ∀ x y z →
      bracket-e₈ x (bracket-e₈ y z) +E8
      (bracket-e₈ y (bracket-e₈ z x) +E8
       bracket-e₈ z (bracket-e₈ x y))
      ≡ ε-zero

    -- G₂ 側の bracket（Derivation 上のリー括弧）
    bracket-g₂ : Derivation → Derivation → Derivation

    -- G₂ の E₈ への埋め込み
    g₂-embedding : Derivation → e₈

    -- 埋め込みが Lie 準同型であること
    g₂-compat : ∀ D₁ D₂ →
      bracket-e₈ (g₂-embedding D₁) (g₂-embedding D₂)
      ≡ g₂-embedding (bracket-g₂ D₁ D₂)

