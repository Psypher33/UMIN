{-# OPTIONS --cubical --guardedness #-}

open import Cubical.Foundations.Prelude

module UMIN.L02_Phys.RH.CocycleToLoc (X : Set₀) (V : Set₀) (isSetV : isSet V) where

open import Cubical.Foundations.Equiv

open import UMIN.L01_Math.RH.Base X V
open import UMIN.L02_Phys.RH.Fiber X V
open import UMIN.L02_Phys.RH.TotalFiberTriv X V isSetV

------------------------------------------------------------------------
-- Cocycle→Loc-global の完全実装
-- carrier = TotalFiber Cov C x
-- triv    = TotalFiber-triv i ui
-- postulate ゼロ！
------------------------------------------------------------------------

Cocycle→Loc-global : (Cov : Covering) → Cocycle Cov → LocalSystem
Cocycle→Loc-global Cov C = record
  { Cov   = Cov
  ; F     = λ x → TotalFiber Cov C x
  ; F-set = λ _ → TotalFiber-isSet
  ; triv  = λ i x ui → TotalFiber-triv {Cov = Cov} {C = C} {x = x} i ui
  }

------------------------------------------------------------------------
-- cocycle-reconstruct：
-- Loc→Cocycle (Cocycle→Loc-global Cov C) ≡ C
--
-- g (Loc→Cocycle (Cocycle→Loc-global Cov C)) i j x (ui , uj)
-- = compEquiv
--     (invEquiv (TotalFiber-triv i ui))
--     (TotalFiber-triv j uj)
--
-- equivFun のレベルで計算：
--   v ↦ TotalFiber-to-V j uj (TotalFiber-from-V i ui v)
--     = TotalFiber-to-V j uj (base i ui v)
--     = equivFun (g C i j x (ui , uj)) v   ← 定義から！
------------------------------------------------------------------------

cocycle-reconstruct :
  (Cov : Covering) (C : Cocycle Cov)
  (i j : Index Cov) (x : X)
  (ui : U Cov i x) (uj : U Cov j x) →
  g (Loc→Cocycle (Cocycle→Loc-global Cov C)) i j x (ui , uj)
  ≡ g C i j x (ui , uj)
cocycle-reconstruct Cov C i j x ui uj =
  equivEq (funExt λ v → refl)