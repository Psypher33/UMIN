{-# OPTIONS --cubical --guardedness --safe #-}

module UMIN.L03_Func.YBE.SU2q_RMatrix where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List
open import Cubical.Data.Int
open import Cubical.Data.Prod
open import UMIN.L03_Func.YBE.LaurentPoly

-- =========================================================
-- Phase 2: SU(2)q 物理モデルと R行列の実装
-- =========================================================

data Spin : Type ℓ-zero where
  up   : Spin
  down : Spin

Basis2 : Type ℓ-zero
Basis2 = Spin × Spin

Basis3 : Type ℓ-zero
Basis3 = Spin × Spin × Spin

μ : Spin → LaurentPoly
μ up   = poly (negsuc 1) (negsuc 0 ∷ [])
μ down = poly (pos 2) (negsuc 0 ∷ [])

ε-cap : Spin → Spin → LaurentPoly
ε-cap up   down = A⁻¹
ε-cap down up   = -A
ε-cap _    _    = poly (pos 0) []

ε-cup : Spin → Spin → LaurentPoly
ε-cup up   down = -A⁻¹
ε-cup down up   = A
ε-cup _    _    = poly (pos 0) []

δ : Spin → Spin → LaurentPoly
δ up   up   = poly (pos 0) (pos 1 ∷ [])
δ down down = poly (pos 0) (pos 1 ∷ [])
δ _    _    = poly (pos 0) []

Matrix2 : Type ℓ-zero
Matrix2 = Basis2 × Basis2 → LaurentPoly

id2 : Matrix2
id2 ((k , l) , (i , j)) = (δ k i) *P (δ l j)

U-mat : Matrix2
U-mat ((k , l) , (i , j)) = (ε-cap k l) *P (ε-cup i j)

R-mat : Matrix2
R-mat (out , inp) = (A *P id2 (out , inp)) +P (A⁻¹ *P U-mat (out , inp))

R12 : Basis3 × Basis3 → LaurentPoly
R12 ((o1 , (o2 , o3)) , (j1 , (j2 , j3))) = R-mat ((o1 , o2) , (j1 , j2)) *P δ o3 j3

R23 : Basis3 × Basis3 → LaurentPoly
R23 ((o1 , (o2 , o3)) , (j1 , (j2 , j3))) = δ o1 j1 *P R-mat ((o2 , o3) , (j2 , j3))