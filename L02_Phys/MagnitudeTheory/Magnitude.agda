{-# OPTIONS --cubical --guardedness #-}

module UMIN.L02_Phys.MagnitudeTheory.Magnitude where

open import Cubical.Foundations.Prelude
open import Agda.Builtin.Float
open import Cubical.Data.Nat
open import Cubical.Data.Vec.Base
open import Cubical.Data.Bool
open import Cubical.Data.FinData

-- 浮動小数点の演算子
private
  _-f_ : Float → Float → Float
  _-f_ = primFloatMinus
  
  _*f_ : Float → Float → Float
  _*f_ = primFloatTimes
  
  _/f_ : Float → Float → Float
  _/f_ = primFloatDiv
  
  _+f_ : Float → Float → Float
  _+f_ = primFloatPlus
  
  sqrt : Float → Float
  sqrt = primFloatSqrt

-- 【救策】tabulate が見つからないため、ここで定義します
-- インデックス(Fin n)を受け取って要素を返す関数から Vec を作ります
tabulate : ∀ {ℓ} {A : Set ℓ} {n : ℕ} → (Fin n → A) → Vec A n
tabulate {n = zero} f = []
tabulate {n = suc n} f = f zero ∷ tabulate (λ x → f (suc x))

-- 行列の型定義
Matrix : ℕ → Set
Matrix n = Vec (Vec Float n) n

module MagnitudeOps (n : ℕ) where

  -- 1. 行列の全要素の総和
  matrix-sum : Matrix n → Float
  matrix-sum m = foldr (λ row acc → foldr (λ x s → x +f s) acc row) 0.0 m

  -- 2. 単位行列の生成
  identity-matrix : Matrix n
  identity-matrix = tabulate λ i → tabulate λ j → 
    if (i == j) then 1.0 else 0.0

  -- 3. Normalized Distortion
  normalized-distortion : Matrix n → Float
  normalized-distortion Z = 
    let 
      dimF  = primNatToFloat n
      scale = sqrt (dimF *f (dimF -f 1.0))
      
      sum-sq : Float → Vec Float n → Float
      sum-sq acc row = foldr (λ x s → (x *f x) +f s) acc row
      
      diff-matrix = tabulate λ i → tabulate λ j → 
        lookup i (lookup j Z) -f lookup i (lookup j identity-matrix)
        
      total-diff-sq = foldr (λ row acc → sum-sq acc row) 0.0 diff-matrix
      
    in if (primFloatLess 0.0 scale) then (sqrt total-diff-sq) /f scale else 0.0

  -- 4. Leinster Magnitude
  postulate 
    inverse-op : Matrix n → Matrix n 

  leinster-magnitude : Matrix n → Float
  leinster-magnitude Z = matrix-sum (inverse-op Z)
