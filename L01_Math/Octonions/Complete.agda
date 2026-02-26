{-# OPTIONS --cubical --safe --guardedness #-}

module UMIN.L01_Math.Octonions.Complete where

open import Cubical.Foundations.Prelude
open import Agda.Builtin.Float

-- =========================================================
-- Float Operators Alias (v2.8.0 準拠)
-- =========================================================
infixl 7 _*_
infixl 6 _+_ _-_

_+_ = primFloatPlus
_-_ = primFloatMinus
_*_ = primFloatTimes

-- =========================================================
-- Octonion Definition (8-dimensional ℝ-algebra)
-- =========================================================

record Octonion : Type where
  constructor mkOct
  field
    e₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ : Float

-- =========================================================
-- Fano Plane Multiplication Table
-- =========================================================

_*Oct_ : Octonion → Octonion → Octonion
mkOct a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ *Oct mkOct b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ = 
  mkOct c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇
  where
    c₀ = a₀ * b₀ - a₁ * b₁ - a₂ * b₂ - a₃ * b₃ - a₄ * b₄ - a₅ * b₅ - a₆ * b₆ - a₇ * b₇
    c₁ = a₀ * b₁ + a₁ * b₀ + a₂ * b₄ - a₃ * b₇ - a₄ * b₂ + a₅ * b₆ - a₆ * b₅ + a₇ * b₃
    c₂ = a₀ * b₂ - a₁ * b₄ + a₂ * b₀ + a₃ * b₅ + a₄ * b₁ - a₅ * b₃ + a₆ * b₇ - a₇ * b₆
    c₃ = a₀ * b₃ + a₁ * b₇ - a₂ * b₅ + a₃ * b₀ - a₄ * b₆ + a₅ * b₂ - a₆ * b₄ + a₇ * b₁
    c₄ = a₀ * b₄ + a₁ * b₂ - a₂ * b₁ + a₃ * b₆ + a₄ * b₀ - a₅ * b₇ + a₆ * b₃ - a₇ * b₅
    c₅ = a₀ * b₅ - a₁ * b₆ + a₂ * b₃ - a₃ * b₂ + a₄ * b₇ + a₅ * b₀ - a₆ * b₁ + a₇ * b₄
    c₆ = a₀ * b₆ + a₁ * b₅ - a₂ * b₇ + a₃ * b₄ - a₄ * b₃ + a₅ * b₁ + a₆ * b₀ - a₇ * b₂
    c₇ = a₀ * b₇ - a₁ * b₃ + a₂ * b₆ - a₃ * b₁ + a₄ * b₅ - a₅ * b₄ + a₆ * b₂ + a₇ * b₀

-- =========================================================
-- Basic Operations & Properties
-- =========================================================

_+Oct_ : Octonion → Octonion → Octonion
mkOct a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ +Oct mkOct b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ =
  mkOct (a₀ + b₀) (a₁ + b₁) (a₂ + b₂) (a₃ + b₃) (a₄ + b₄) (a₅ + b₅) (a₆ + b₆) (a₇ + b₇)

_-Oct_ : Octonion → Octonion → Octonion
mkOct a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ -Oct mkOct b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ =
  mkOct (a₀ - b₀) (a₁ - b₁) (a₂ - b₂) (a₃ - b₃) (a₄ - b₄) (a₅ - b₅) (a₆ - b₆) (a₇ - b₇)

normSq : Octonion → Float
normSq (mkOct x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇) = 
  (x₀ * x₀) + (x₁ * x₁) + (x₂ * x₂) + (x₃ * x₃) + 
  (x₄ * x₄) + (x₅ * x₅) + (x₆ * x₆) + (x₇ * x₇)

-- primFloatSqrt はライブラリから自動取得されるため定義不要になりました
norm : Octonion → Float
norm x = primFloatSqrt (normSq x)

associator : Octonion → Octonion → Octonion → Octonion
associator x y z = ((x *Oct y) *Oct z) -Oct (x *Oct (y *Oct z))

-- =========================================================
-- Basis Elements
-- =========================================================

be₀ be₁ be₂ be₃ be₄ be₅ be₆ be₇ : Octonion
be₀ = mkOct 1.0 0.0 0.0 0.0 0.0 0.0 0.0 0.0
be₁ = mkOct 0.0 1.0 0.0 0.0 0.0 0.0 0.0 0.0
be₂ = mkOct 0.0 0.0 1.0 0.0 0.0 0.0 0.0 0.0
be₃ = mkOct 0.0 0.0 0.0 1.0 0.0 0.0 0.0 0.0
be₄ = mkOct 0.0 0.0 0.0 0.0 1.0 0.0 0.0 0.0
be₅ = mkOct 0.0 0.0 0.0 0.0 0.0 1.0 0.0 0.0
be₆ = mkOct 0.0 0.0 0.0 0.0 0.0 0.0 1.0 0.0
be₇ = mkOct 0.0 0.0 0.0 0.0 0.0 0.0 0.0 1.0

-- =========================================================
-- Exported Interface
-- =========================================================

open Octonion public