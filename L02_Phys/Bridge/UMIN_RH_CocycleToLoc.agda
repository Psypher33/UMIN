{-# OPTIONS --cubical --guardedness #-}

module UMIN.L02_Phys.Bridge.UMIN_RH_CocycleToLoc (X : Set₀) (V : Set₀) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.HITs.PropositionalTruncation as PT

open import UMIN.L01_Math.Geometry.UMIN_RH_Base X V
open import UMIN.L02_Phys.Bridge.UMIN_RH_Fiber X V
open import UMIN.L02_Phys.Bridge.UMIN_RH_TotalFiberTriv X V

------------------------------------------------------------------------
-- Cocycle→Loc-global の実装
-- 各点ファイバーは V（方針 A）
-- triv は型を合わせて恒等同値
------------------------------------------------------------------------

Cocycle→Loc-global : (Cov : Covering) → Cocycle Cov → LocalSystem
Cocycle→Loc-global Cov C = record
  { Cov   = Cov
  ; F     = λ _ → V
  ; F-set = λ _ → isSetV
  ; triv  = λ _ _ _ → idEquiv V
  }

------------------------------------------------------------------------
-- triv-def：方針Aでは postulate として保持
------------------------------------------------------------------------

postulate
  triv-def :
    (Cov : Covering) (C : Cocycle Cov)
    (i j : Index Cov) (x : X)
    (ui : U Cov i x) (uj : U Cov j x) →
    equivFun (triv (Cocycle→Loc-global Cov C) j x uj)
      ≡
    λ v → equivFun (g C i j x (ui , uj))
            (equivFun (triv (Cocycle→Loc-global Cov C) i x ui) v)