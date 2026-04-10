{-# OPTIONS --cubical --guardedness --safe #-}

open import Cubical.Foundations.Prelude

module UMIN.L02_Phys.Bridge.UMIN_RH_TotalFiberTriv (X : Set₀) (V : Set₀) (isSetV : isSet V) where
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels using (isOfHLevelPath')
open import Cubical.Foundations.Isomorphism
  using (Iso ; iso ; isoToEquiv)

open import UMIN.L01_Math.Geometry.UMIN_RH_Base X V
open import UMIN.L02_Phys.Bridge.UMIN_RH_Fiber X V

------------------------------------------------------------------------
-- to 方向：TotalFiber → V
-- base j uj v ↦ equivFun (g C j i x (uj , ui)) v
------------------------------------------------------------------------

TotalFiber-to-V :
  {Cov : Covering} {C : Cocycle Cov} {x : X}
  (i : Index Cov) (ui : U Cov i x) →
  TotalFiber Cov C x → V
TotalFiber-to-V {Cov} {C} {x} i ui =
  TotalFiber-elim {Cov} {c = C} {x = x}
    (λ _ → isSetV)
    (λ j uj v → equivFun (g C j i x (uj , ui)) v)
    (λ j k uj uk v →
      sym (funExt⁻ (cong equivFun
        (g-comp C j k i x uj uk ui)) v))

------------------------------------------------------------------------
-- from 方向：V → TotalFiber
-- v ↦ base i ui v
------------------------------------------------------------------------

TotalFiber-from-V :
  {Cov : Covering} {C : Cocycle Cov} {x : X}
  (i : Index Cov) (ui : U Cov i x) →
  V → TotalFiber Cov C x
TotalFiber-from-V {Cov} {C} {x} i ui v =
  base i ui v

------------------------------------------------------------------------
-- section：to ∘ from = id
-- TotalFiber-to-V i ui (base i ui v)
-- = equivFun (g C i i x (ui , ui)) v
-- = equivFun (idEquiv V) v   ← g-id
-- = v
------------------------------------------------------------------------

TotalFiber-triv-sec :
  {Cov : Covering} {C : Cocycle Cov} {x : X}
  (i : Index Cov) (ui : U Cov i x) (v : V) →
  TotalFiber-to-V {Cov} {C} {x} i ui (TotalFiber-from-V {Cov} {C} {x} i ui v) ≡ v
TotalFiber-triv-sec {Cov} {C} {x} i ui v =
  funExt⁻ (cong equivFun (g-id C i x ui)) v

------------------------------------------------------------------------
-- retraction：from ∘ to = id
-- base i ui (TotalFiber-to-V i ui t) ≡ t
------------------------------------------------------------------------

TotalFiber-triv-ret :
  {Cov : Covering} {C : Cocycle Cov} {x : X}
  (i : Index Cov) (ui : U Cov i x)
  (t : TotalFiber Cov C x) →
  TotalFiber-from-V i ui (TotalFiber-to-V i ui t) ≡ t
TotalFiber-triv-ret {Cov} {C} {x} i ui =
  TotalFiber-elim {Cov} {c = C} {x = x}
    (λ t →
      isProp→isSet
        (isOfHLevelPath' 1
          (TotalFiber-isSet {Cov = Cov} {c = C} {x = x})
          (base i ui (TotalFiber-to-V {Cov} {C} {x} i ui t))
          t))
    (λ j uj v →
      -- base i ui (equivFun (g C j i ...) v) ≡ base j uj v
      sym (paste j i uj ui v))
    (λ j k uj uk v →
      isProp→PathP
        (λ ℓ →
          TotalFiber-isSet {Cov = Cov} {c = C} {x = x}
            (base i ui
              (TotalFiber-to-V {Cov} {C} {x} i ui
                (paste j k uj uk v ℓ)))
            (paste j k uj uk v ℓ))
        (sym (paste j i uj ui v))
        (sym (paste k i uk ui
          (equivFun (g C j k x (uj , uk)) v))))

------------------------------------------------------------------------
-- TotalFiber-triv：同値の完成
------------------------------------------------------------------------

TotalFiber-triv :
  {Cov : Covering} {C : Cocycle Cov} {x : X}
  (i : Index Cov) (ui : U Cov i x) →
  TotalFiber Cov C x ≃ V
TotalFiber-triv {Cov} {C} {x} i ui =
  isoToEquiv triv-iso
  where
  triv-iso : Iso (TotalFiber Cov C x) V
  triv-iso =
    iso
      (TotalFiber-to-V {Cov} {C} {x} i ui)
      (TotalFiber-from-V {Cov} {C} {x} i ui)
      (TotalFiber-triv-sec {Cov = Cov} {C = C} {x = x} i ui)
      (TotalFiber-triv-ret {Cov = Cov} {C = C} {x = x} i ui)