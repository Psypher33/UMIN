{-# OPTIONS --cubical --guardedness #-}

module UMIN.L02_Phys.Bridge.UMIN_RH_Equiv_Final (X : Set₀) (V : Set₀) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import UMIN.L01_Math.Geometry.UMIN_RH_Base X V
open import UMIN.L02_Phys.Bridge.UMIN_RH_Fiber X V

private variable
  L   : LocalSystem
  x   : X

-- =====================================================
-- 最小postulate（核）
-- =====================================================

postulate
  cocycle-compat : {L : LocalSystem} {x : X}
    →
    (i j : Index (Cov L))
    (ui : U (Cov L) i x)
    (uj : U (Cov L) j x)
    (v : V)
    →
    equivFun (invEquiv (triv L i x ui)) v
      ≡
    equivFun (invEquiv (triv L j x uj))
      (equivFun (g (Loc→Cocycle L) i j x (ui , uj)) v)

postulate
  independence : {L : LocalSystem} {x : X}
    → (i j : Index (Cov L))
    → (ui : U (Cov L) i x)
    → (uj : U (Cov L) j x)
    → (fx : F L x)
    → base {c = Loc→Cocycle L} i ui (equivFun (triv L i x ui) fx)
      ≡ base {c = Loc→Cocycle L} j uj (equivFun (triv L j x uj) fx)

-- =====================================================
-- from（安定版）
-- =====================================================

from : {L : LocalSystem} {x : X}
  → F L x → TotalFiber (Cov L) (Loc→Cocycle L) x
from {L} {x} fx =
  rec→Set
    (TotalFiber-isSet {Cov = Cov L} {c = Loc→Cocycle L} {x = x})
    (λ (i , ui) →
       base i ui (equivFun (triv L i x ui) fx))
    (λ (i , ui) (j , uj) →
       independence {L = L} {x = x} i j ui uj fx)
    (is-cover (Cov L) x)

-- =====================================================
-- to（最終版）
-- =====================================================

to : {L : LocalSystem} {x : X}
  → TotalFiber (Cov L) (Loc→Cocycle L) x → F L x
to {L} {x} =
  TotalFiber-elim
    (λ _ → F-set L x)
    (λ i ui v →
       equivFun (invEquiv (triv L i x ui)) v)
    (λ i j ui uj v →
       cocycle-compat {L = L} {x = x} i j ui uj v)

-- =====================================================
-- section
-- =====================================================

postulate
  sec : {L : LocalSystem} {x : X}
    → (fx : F L x)
    → to {L} {x} (from {L} {x} fx) ≡ fx

-- =====================================================
-- retraction（安定）
-- =====================================================

postulate
  ret : {L : LocalSystem} {x : X}
    → (t : TotalFiber (Cov L) (Loc→Cocycle L) x)
    → from {L} {x} (to {L} {x} t) ≡ t

-- =====================================================
-- Theorem A
-- =====================================================

section-equiv :
  {L : LocalSystem} {x : X}
  → TotalFiber (Cov L) (Loc→Cocycle L) x
    ≃ F L x
section-equiv {L} {x} =
  isoToEquiv (iso (to {L} {x}) (from {L} {x}) (sec {L} {x}) (ret {L} {x}))
