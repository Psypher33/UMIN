{-# OPTIONS --cubical --safe --guardedness #-}

open import Cubical.Algebra.Ring

module UMIN.L00_Core.Algebra.FPS_Properties {ℓ} (R : Ring ℓ) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; _∸_)

open import UMIN.L00_Core.Logic.EquationEngine
open import UMIN.L00_Core.Algebra.FPS_Base R

open RingStr (snd R) renaming
  ( _+_  to _+R_
  ; _·_  to _*R_
  ; 0r   to 0R
  ; 1r   to 1R )

private
  Carrier : Type ℓ
  Carrier = fst R

-- =======================================================================
-- 1. 加法の基本性質
-- =======================================================================

-- 加法の交換律（FPS レベル）
⊞-comm : (A B : FormalPowerSeries)
        → A ⊞ B ≡ B ⊞ A
⊞-comm A B = fps-ext λ n →
  RingStr.+Comm (snd R) (A n) (B n)

-- 加法の結合律（FPS レベル）
⊞-assoc : (A B C : FormalPowerSeries)
         → (A ⊞ B) ⊞ C ≡ A ⊞ (B ⊞ C)
⊞-assoc A B C = fps-ext λ n →
  sym (RingStr.+Assoc (snd R) (A n) (B n) (C n))

-- =======================================================================
-- 2. スカラー倍の基本性質
-- =======================================================================

-- スカラー倍の分配律（加法に対して）
⊙-distrib-⊞ : (r : Carrier) (A B : FormalPowerSeries)
             → r ⊙ (A ⊞ B) ≡ (r ⊙ A) ⊞ (r ⊙ B)
⊙-distrib-⊞ r A B = fps-ext λ n →
  RingStr.·DistR+ (snd R) r (A n) (B n)

-- =======================================================================
-- 3. *P の基本性質
-- =======================================================================

-- *P の refl（両辺が refl なら結果も refl）
*P-refl : {A B : Carrier}
        → refl {x = A} *P refl {x = B} ≡ refl
*P-refl = refl

-- *P の sym（両辺を反転）
*P-sym : {A A' B B' : Carrier}
       → (p : A ≡ A') (q : B ≡ B')
       → sym p *P sym q ≡ sym (p *P q)
*P-sym p q = refl

-- =======================================================================
-- 4. 将来の接続点（TODO）
-- =======================================================================
-- 以下は FPSCategory（層3）が完成した後に実装する：
--
-- Cauchy 積の単位元
-- fps-unit : FormalPowerSeries
-- fps-unit 0 = 1R
-- fps-unit _ = 0R
--
-- Cauchy 積と単位元の関係
-- cauchy-unit-left  : (A : FormalPowerSeries) → fps-unit ⊠ A ≡ A
-- cauchy-unit-right : (A : FormalPowerSeries) → A ⊠ fps-unit ≡ A