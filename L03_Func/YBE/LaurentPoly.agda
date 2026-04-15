{-# OPTIONS --cubical --guardedness --safe #-}

module UMIN.L03_Func.YBE.LaurentPoly where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List
open import Cubical.Data.Int renaming (_·_ to _·ℤ_)
open import Cubical.Data.Nat renaming (_+_ to _+N_)
open import Cubical.Data.Bool

-- =========================================================
-- Phase 1: 計算可能なローラン多項式環 Z[A, A⁻¹]
-- =========================================================

record LaurentPoly : Type ℓ-zero where
  constructor poly
  field
    offset : ℤ
    coeffs : List ℤ

-- ゼロ判定ヘルパー
isZeroℤ : ℤ → Bool
isZeroℤ (pos 0) = true
isZeroℤ _       = false

dropWhileZero : List ℤ → List ℤ
dropWhileZero [] = []
dropWhileZero (x ∷ xs) with isZeroℤ x
... | true  = dropWhileZero xs
... | false = x ∷ xs

-- 正規化
normalize : ℤ → List ℤ → LaurentPoly
normalize off [] = poly (pos 0) []
normalize off (pos 0 ∷ xs) = normalize (off + pos 1) xs
normalize off xs = 
  let 
    trimmed = rev (dropWhileZero (rev xs))
  in poly off trimmed

-- 加算ヘルパー
padLeft : ℕ → List ℤ → List ℤ
padLeft 0       xs = xs
padLeft (suc n) xs = pos 0 ∷ padLeft n xs

addCoeffs : List ℤ → List ℤ → List ℤ
addCoeffs []       ys       = ys
addCoeffs xs       []       = xs
addCoeffs (x ∷ xs) (y ∷ ys) = (x + y) ∷ addCoeffs xs ys

is-nonneg : ℤ → Bool
is-nonneg (pos _)    = true
is-nonneg (negsuc _) = false

abs-diff : ℤ → ℕ
abs-diff (pos n)    = n
abs-diff (negsuc n) = suc n

_+P_ : LaurentPoly → LaurentPoly → LaurentPoly
poly o1 c1 +P poly o2 c2 =
  let
    diff = o2 - o1
  in
  if is-nonneg diff
    then normalize o1 (addCoeffs c1 (padLeft (abs-diff diff) c2))
    else normalize o2 (addCoeffs (padLeft (abs-diff (- diff)) c1) c2)

-- 乗算ヘルパー
scaleCoeffs : ℤ → List ℤ → List ℤ
scaleCoeffs s []       = []
scaleCoeffs s (x ∷ xs) = (s ·ℤ x) ∷ scaleCoeffs s xs

convolve : List ℤ → List ℤ → List ℤ
convolve []       _  = []
convolve (x ∷ xs) ys =
  addCoeffs (scaleCoeffs x ys)
            (pos 0 ∷ convolve xs ys)

_*P_ : LaurentPoly → LaurentPoly → LaurentPoly
poly o1 c1 *P poly o2 c2 =
  normalize (o1 + o2) (convolve c1 c2)

-- 量子パラメータ
A : LaurentPoly
A = poly (pos 1) (pos 1 ∷ [])

A⁻¹ : LaurentPoly
A⁻¹ = poly (negsuc 0) (pos 1 ∷ [])

-A : LaurentPoly
-A = poly (pos 1) (negsuc 0 ∷ [])

-A⁻¹ : LaurentPoly
-A⁻¹ = poly (negsuc 0) (negsuc 0 ∷ [])

-- 正規化テスト
normalize-test-1 : normalize (pos 0) (pos 0 ∷ pos 1 ∷ []) ≡ poly (pos 1) (pos 1 ∷ [])
normalize-test-1 = refl

normalize-test-2 : normalize (pos 0) [] ≡ poly (pos 0) []
normalize-test-2 = refl