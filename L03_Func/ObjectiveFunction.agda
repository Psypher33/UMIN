{-# OPTIONS --cubical --guardedness #-}

module UMIN.L03_Func.ObjectiveFunction where

open import Cubical.Foundations.Prelude
open import Agda.Builtin.Float
open import Cubical.Data.Nat
open import Cubical.Data.Vec.Base
open import Cubical.Data.Bool

open import UMIN.L03_Func.MagnitudeTheory

-- Float演算子の再定義（ObjectiveFunction内でも必要です）
private
  _+f_ : Float → Float → Float
  _+f_ = primFloatPlus
  
  _*f_ : Float → Float → Float
  _*f_ = primFloatTimes
  
  _-f_ : Float → Float → Float
  _-f_ = primFloatMinus
  
  _/f_ : Float → Float → Float
  _/f_ = primFloatDiv

  pow : Float → Float → Float
  pow = primFloatPow

module ObjectiveOps (n : ℕ) where

  open MagnitudeOps n

  postulate
    determinant : Matrix n → Float

  szpiro-penalty : Matrix n → Float
  szpiro-penalty Z = 
    let 
      det = determinant Z
      epsilon = 1.0e-9
      large-penalty = 1.0e12 
    in if (primFloatLess det epsilon) 
       then large-penalty 
       else (1.0 /f det)

  objective-function : Matrix n → (λ-coeff : Float) → Float
  objective-function Z λ-coeff =
    let 
      mag  = leinster-magnitude Z
      dist = normalized-distortion Z
      pen  = (szpiro-penalty Z) *f 0.5
      complexity = (mag *f pow dist λ-coeff)
    in complexity -f pen