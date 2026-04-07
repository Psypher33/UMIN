{-# OPTIONS --cubical --guardedness #-}
module UMIN.L02_Phys.Bridge.UMIN_RH_Equiv (X : Set₀) (V : Set₀) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import UMIN.L01_Math.Geometry.UMIN_RH_Base X V
open import UMIN.L02_Phys.Bridge.UMIN_RH_Fiber X V

postulate
  -- to / from の定義（骨格）
  to : {Cov : Covering} {L : LocalSystem} {x : X}
     → TotalFiber Cov (Loc→Cocycle Cov L) x
     → carrier (F L x)

  from : {Cov : Covering} {L : LocalSystem} {x : X}
       → carrier (F L x)
       → TotalFiber Cov (Loc→Cocycle Cov L) x

  -- section（to ∘ from = id）
  sec : {Cov : Covering} {L : LocalSystem} {x : X}
      → (fx : carrier (F L x))
      → to {Cov} {L} {x} (from {Cov} {L} {x} fx) ≡ fx

-- ==========================================
-- retraction と section-equiv の骨格
-- ==========================================
postulate
  ret : {Cov : Covering} {L : LocalSystem} {x : X}
      → (t : TotalFiber Cov (Loc→Cocycle Cov L) x)
      → from {Cov} {L} {x} (to {Cov} {L} {x} t) ≡ t

section-equiv : (Cov : Covering) (L : LocalSystem) (x : X)
              → TotalFiber Cov (Loc→Cocycle Cov L) x ≃ carrier (F L x)
section-equiv Cov L x =
  isoToEquiv (iso
    (to {Cov = Cov} {L = L} {x = x})
    (from {Cov = Cov} {L = L} {x = x})
    (sec {Cov = Cov} {L = L} {x = x})
    (ret {Cov = Cov} {L = L} {x = x}))

postulate
  UMIN-RH-Equivalence : (Cov : Covering) → Cocycle Cov ≃ LocalSystem