{-# OPTIONS --cubical --safe --guardedness #-}

module UMIN.L00_Foundation.HomotopyTheory.HomotopyFiber where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_)
open import UMIN.L00_Foundation.HomotopyTheory.Pointed

--------------------------------------------------
-- 1. Pointed homotopy fiber（Psypher スケルトン）
--------------------------------------------------

hofibPt : {A B : Pointed} (F : PointedMap A B) → Pointed
hofibPt {A} {B} F = record
  { Space = Σ[ a ∈ Pointed.Space A ]
              (PointedMap.f F a ≡ Pointed.pt B)
  ; pt    = (Pointed.pt A , PointedMap.pt-pres F)
  }

--------------------------------------------------
-- 2. 射影 pr1
--------------------------------------------------

pr1-map : {A B : Pointed} (F : PointedMap A B)
        → PointedMap (hofibPt F) A
pr1-map F = record
  { f       = fst
  ; pt-pres = refl
  }

--------------------------------------------------
-- 3. pr2：ファイバーの path 成分へのアクセス
--------------------------------------------------

pr2-path : {A B : Pointed} (F : PointedMap A B)
         → (x : Pointed.Space (hofibPt F))
         → PointedMap.f F (fst x) ≡ Pointed.pt B
pr2-path F x = snd x

--------------------------------------------------
-- 4. hofibPt の基点の path 成分
--------------------------------------------------

hofib-pt-path : {A B : Pointed} (F : PointedMap A B)
              → PointedMap.f F (Pointed.pt A) ≡ Pointed.pt B
hofib-pt-path F = PointedMap.pt-pres F

--------------------------------------------------
-- 5. π₀(hofib(F)) の非自明性の型（TremblingCore 条件）
--
-- ※ 指示書 §5 の指示通り、postulate にしない。
--   witness の存在は LGT 側で提供される前提で、
--   型のみを記述する。
--------------------------------------------------

TremblingCore-witness : {A B : Pointed} (F : PointedMap A B)
                      → Type₀
TremblingCore-witness {A} {B} F =
  Σ[ x ∈ Pointed.Space (hofibPt F) ]
    (¬ (x ≡ Pointed.pt (hofibPt F)))
