{-# OPTIONS --cubical --guardedness --safe #-}

module UMIN.L03_Func.YBE.Jones_Final_Emergence where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List
open import Cubical.Data.Prod
open import Cubical.Data.Int
open import UMIN.L03_Func.YBE.LaurentPoly
open import UMIN.L03_Func.YBE.SU2q_RMatrix

-- =========================================================
-- Phase 2.5: 高速化ヘルパー（ゼロのショートサーキット）
-- =========================================================
-- R行列は非常に疎（ほとんどの成分が0）であるため、
-- 計算前に0を弾くことでAgdaのコンパイルスタックを防ぎます。

zeroP : LaurentPoly
zeroP = poly (pos 0) []

-- ショートサーキット乗算（どちらかが0なら即座に0を返す）
_*P-fast_ : LaurentPoly → LaurentPoly → LaurentPoly
poly _ [] *P-fast y = zeroP
x *P-fast poly _ [] = zeroP
x *P-fast y = x *P y

-- ショートサーキット加算（片方が0なら計算せずにもう片方を返す）
_+P-fast_ : LaurentPoly → LaurentPoly → LaurentPoly
poly _ [] +P-fast y = y
x +P-fast poly _ [] = x
x +P-fast y = x +P y

-- =========================================================
-- Phase 3: YBE 特化回路 (n=3) と段階的評価
-- =========================================================

AllStates : List Basis3
AllStates = (up , up , up) ∷ (up , up , down) ∷ (up , down , up) ∷ (up , down , down) ∷
            (down , up , up) ∷ (down , up , down) ∷ (down , down , up) ∷ (down , down , down) ∷ []

-- リスト上の再帰計算（0を弾きながら足し込む）
calc-L1 : Basis3 → Basis3 → List Basis3 → LaurentPoly
calc-L1 out inp [] = zeroP
calc-L1 out inp (s ∷ ss) = 
  (R12 (out , s) *P-fast R23 (s , inp)) +P-fast calc-L1 out inp ss

calc-R1 : Basis3 → Basis3 → List Basis3 → LaurentPoly
calc-R1 out inp [] = zeroP
calc-R1 out inp (s ∷ ss) = 
  (R23 (out , s) *P-fast R12 (s , inp)) +P-fast calc-R1 out inp ss

L1-entry : Basis3 → Basis3 → LaurentPoly
L1-entry out inp = calc-L1 out inp AllStates

R1-entry : Basis3 → Basis3 → LaurentPoly
R1-entry out inp = calc-R1 out inp AllStates

-- =========================================================
-- Phase 4: 最終観測 (YBE: L1 ∘ R12 ≡ R1 ∘ R23)
-- =========================================================

calc-L-final : Basis3 → Basis3 → List Basis3 → LaurentPoly
calc-L-final out inp [] = zeroP
calc-L-final out inp (s ∷ ss) = 
  (L1-entry out s *P-fast R12 (s , inp)) +P-fast calc-L-final out inp ss

calc-R-final : Basis3 → Basis3 → List Basis3 → LaurentPoly
calc-R-final out inp [] = zeroP
calc-R-final out inp (s ∷ ss) = 
  (R1-entry out s *P-fast R23 (s , inp)) +P-fast calc-R-final out inp ss

L-final : Basis3 → Basis3 → LaurentPoly
L-final out inp = calc-L-final out inp AllStates

R-final : Basis3 → Basis3 → LaurentPoly
R-final out inp = calc-R-final out inp AllStates

-- =========================================================
-- 最終検証
-- =========================================================

-- まずは一番シンプルな成分でコンパイルが通るかテスト
YBE-Check-000-000 : L-final (up , up , up) (up , up , up) ≡ R-final (up , up , up) (up , up , up)
YBE-Check-000-000 = refl

-- 成功すれば順次コメントアウトを外してください⭐️
-- YBE-Check-010-101 : L-final (up , down , up) (down , up , down) ≡ R-final (up , down , up) (down , up , down)
-- YBE-Check-010-101 = refl

-- YBE-Check-111-111 : L-final (down , down , down) (down , down , down) ≡ R-final (down , down , down) (down , down , down)
-- YBE-Check-111-111 = refl