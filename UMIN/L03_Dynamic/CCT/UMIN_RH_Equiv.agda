{-# OPTIONS --cubical --guardedness #-}
module UMIN.L03_Dynamic.CCT.UMIN_RH_Equiv (X : Set₀) (V : Set₀) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import UMIN.L01_Arithmetic.Motives.UMIN_RH_Base X V
open import UMIN.L03_Dynamic.CCT.UMIN_RH_Fiber X V

postulate
  -- to / from の定義（骨格）
  to : {L : LocalSystem} {x : X}
     → TotalFiber (Cov L) (Loc→Cocycle L) x
     → F L x

  from : {L : LocalSystem} {x : X}
       → F L x
       → TotalFiber (Cov L) (Loc→Cocycle L) x

  -- section（to ∘ from = id）
  sec : {L : LocalSystem} {x : X}
      → (fx : F L x)
      → to {L} {x} (from {L} {x} fx) ≡ fx

-- ==========================================
-- retraction と section-equiv の骨格
-- ==========================================
postulate
  ret : {L : LocalSystem} {x : X}
      → (t : TotalFiber (Cov L) (Loc→Cocycle L) x)
      → from {L} {x} (to {L} {x} t) ≡ t

section-equiv : (L : LocalSystem) (x : X)
              → TotalFiber (Cov L) (Loc→Cocycle L) x ≃ F L x
section-equiv L x =
  isoToEquiv (iso
    (to {L = L} {x = x})
    (from {L = L} {x = x})
    (sec {L = L} {x = x})
    (ret {L = L} {x = x}))

postulate
  UMIN-RH-Equivalence : (Cov : Covering) → Cocycle Cov ≃ LocalSystem-at Cov
