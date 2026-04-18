{-# OPTIONS --cubical --guardedness #-}

module UMIN.L03_Dynamic.CCT.RH_Equiv_Final (X : Set₀) (V : Set₀) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
  using (isOfHLevelPath' ; isOfHLevel→isOfHLevelDep)
open import Cubical.Foundations.Isomorphism using (Iso ; iso ; isoToEquiv)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import UMIN.L01_Arithmetic.Motives.RH_Base X V
open import UMIN.L03_Dynamic.CCT.RH_Fiber X V

private variable
  L : LocalSystem
  x : X

-- =====================================================
-- independence（postulate 廃止）
-- =====================================================

independence :
  {L : LocalSystem} {x : X}
  (i j : Index (Cov L))
  (ui : U (Cov L) i x)
  (uj : U (Cov L) j x)
  (fx : F L x)
  → base {c = Loc→Cocycle L} i ui
      (equivFun (triv L i x ui) fx)
    ≡ base {c = Loc→Cocycle L} j uj
        (equivFun (triv L j x uj) fx)
independence {L} {x} i j ui uj fx =
  paste i j ui uj (equivFun (triv L i x ui) fx)
  ∙ cong (base j uj)
      (cong (equivFun (triv L j x uj))
        (retEq (triv L i x ui) fx))

-- =====================================================
-- from：F L x → TotalFiber
-- =====================================================

-- is-cover の証明を引数に取る版（sec で PT.elim と同じ被覆に合わせて簡約させる）
fromWithCov :
  (L : LocalSystem) (x : X) (fx : F L x)
  → ∥ Σ[ i ∈ Index (Cov L) ] U (Cov L) i x ∥₁
  → TotalFiber (Cov L) (Loc→Cocycle L) x
fromWithCov L@(record { Cov = _ ; F = _ ; F-set = F-set' ; triv = _ }) x fx cov =
  let _ = F-set' in
  rec→Set
    {B = TotalFiber (Cov L) (Loc→Cocycle L) x}
    (TotalFiber-isSet {Cov = Cov L} {c = Loc→Cocycle L} {x = x})
    {A = Σ[ i ∈ Index (Cov L) ] U (Cov L) i x}
    (λ (i , ui) →
       base i ui (equivFun (triv L i x ui) fx))
    (λ (i , ui) (j , uj) →
       independence {L} {x} i j ui uj fx)
    cov

from :
  (L : LocalSystem) (x : X)
  → F L x → TotalFiber (Cov L) (Loc→Cocycle L) x
from L x fx =
  fromWithCov L x fx (is-cover (Cov L) x)

-- =====================================================
-- to：TotalFiber → F L x
-- =====================================================

to :
  (L : LocalSystem) (x : X)
  → TotalFiber (Cov L) (Loc→Cocycle L) x → F L x
to L x (base i ui v) =
  invEq (triv L i x ui) v
to L x (paste i j ui uj v k) =
  let
    ti = triv L i x ui
    tj = triv L j x uj
    gij-v = equivFun (compEquiv (invEquiv ti) tj) v
    glue-compat : equivFun (invEquiv ti) v ≡ equivFun (invEquiv tj) gij-v
    glue-compat = sym (retEq tj (equivFun (invEquiv ti) v))
  in
  glue-compat k
to L x (trunc t1 t2 p1 p2 k1 k2) =
  let
    h : (t : TotalFiber (Cov L) (Loc→Cocycle L) x) → isSet (F L x)
    h = λ _ → F-set L x
  in
  isOfHLevel→isOfHLevelDep 2 h (to L x t1) (to L x t2)
    (cong (to L x) p1) (cong (to L x) p2) (trunc t1 t2 p1 p2) k1 k2

-- =====================================================
-- section：to ∘ from = id（postulate 廃止）
-- =====================================================

sec :
  (L : LocalSystem) (x : X)
  (fx : F L x)
  → to L x (from L x fx) ≡ fx
sec L x fx =
  PT.elim
    (λ cov →
      isOfHLevelPath' 1 (F-set L x) (to L x (fromWithCov L x fx cov)) fx)
    (λ (i , ui) → retEq (triv L i x ui) fx)
    (is-cover (Cov L) x)

-- =====================================================
-- retraction：from ∘ to = id（postulate 廃止）
-- =====================================================

ret :
  (L : LocalSystem) (x : X)
  (t : TotalFiber (Cov L) (Loc→Cocycle L) x)
  → from L x (to L x t) ≡ t
ret L x (base i ui v) =
  let
    ti = triv L i x ui
    w = invEq ti v
    q : to L x (base i ui v) ≡ w
    q = refl
    core : fromWithCov L x w (is-cover (Cov L) x) ≡ base i ui v
    core =
      PT.elim
        (λ cov →
          isOfHLevelPath' 1 TotalFiber-isSet
            (fromWithCov L x w cov)
            (base i ui v))
        (λ (j , uj) →
          let
            tj = triv L j x uj
            step1 : equivFun ti w ≡ v
            step1 = secEq ti v
            step2 : base j uj (equivFun tj w) ≡ base i ui (equivFun ti w)
            step2 = sym (independence {L} {x} i j ui uj w)
            step3 : base i ui (equivFun ti w) ≡ base i ui v
            step3 = cong (base i ui) step1
          in
          step2 ∙ step3)
        (is-cover (Cov L) x)
  in
  cong (λ z → fromWithCov L x z (is-cover (Cov L) x)) q ∙ core
ret L x (paste i j ui uj v k) =
  isOfHLevel→isOfHLevelDep 1
    (λ t →
      isOfHLevelPath' 1 TotalFiber-isSet (from L x (to L x t)) t)
    (ret L x (base i ui v))
    (ret L x (base j uj (equivFun (g (Loc→Cocycle L) i j x (ui , uj)) v)))
    (paste i j ui uj v)
    k
ret L x (trunc t1 t2 p1 p2 k1 k2) =
  isOfHLevel→isOfHLevelDep 2
    (λ t →
      isProp→isSet
        (isOfHLevelPath' 1 TotalFiber-isSet (from L x (to L x t)) t))
    (ret L x t1)
    (ret L x t2)
    (cong (ret L x) p1)
    (cong (ret L x) p2)
    (trunc t1 t2 p1 p2)
    k1
    k2

-- =====================================================
-- Theorem A：section-equiv
-- =====================================================

section-equiv :
  {L : LocalSystem} {x : X}
  → TotalFiber (Cov L) (Loc→Cocycle L) x
    ≃ F L x
section-equiv {L} {x} = isoToEquiv theIso
  where
  A = TotalFiber (Cov L) (Loc→Cocycle L) x
  B = F L x
  theIso : Iso A B
  theIso = iso (to L x) (from L x) (sec L x) (ret L x)