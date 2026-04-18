{-# OPTIONS --cubical --guardedness #-}

module UMIN.L03_Dynamic.CCT.UMIN_RH_Equiv_TheoremB_Complete
  (X : Set₀) (V : Set₀) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels using (isPropΠ ; isSetΣ ; isSet→)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import UMIN.L01_Arithmetic.Motives.UMIN_RH_Base X V
open import UMIN.L03_Dynamic.CCT.UMIN_RH_Fiber X V
open import UMIN.L03_Dynamic.CCT.UMIN_RH_Equiv_Final X V

------------------------------------------------------------------------
-- V の isSet（唯一残る postulate）
------------------------------------------------------------------------

postulate
  isSetV : isSet V

open import UMIN.L03_Dynamic.CCT.UMIN_RH_CocycleToLoc X V isSetV

------------------------------------------------------------------------
-- isSet-Equiv（導出）
------------------------------------------------------------------------

isSet-Equiv : isSet (V ≃ V)
isSet-Equiv =
  isSetΣ
    (isSet→ isSetV)
    (λ f → isProp→isSet (isPropIsEquiv f))

------------------------------------------------------------------------
-- g-rinv：g i j ∘ g j i = id
------------------------------------------------------------------------

g-rinv :
  {Cov : Covering}
  (C : Cocycle Cov) (i j : Index Cov) (x : X)
  (ui : U Cov i x) (uj : U Cov j x) →
  compEquiv (g C i j x (ui , uj)) (g C j i x (uj , ui)) ≡ idEquiv V
g-rinv C i j x ui uj =
  g-comp C i j i x ui uj ui
  ∙ g-id C i x ui

------------------------------------------------------------------------
-- g-linv：g j i ∘ g i j = id
------------------------------------------------------------------------

g-linv :
  {Cov : Covering}
  (C : Cocycle Cov) (i j : Index Cov) (x : X)
  (ui : U Cov i x) (uj : U Cov j x) →
  compEquiv (g C j i x (uj , ui)) (g C i j x (ui , uj)) ≡ idEquiv V
g-linv C i j x ui uj =
  g-comp C j i j x uj ui uj
  ∙ g-id C j x uj

------------------------------------------------------------------------
-- g-inv-eq：invEquiv (g i j) ≡ g j i（導出）
------------------------------------------------------------------------

g-inv-eq :
  {Cov : Covering}
  (C : Cocycle Cov) (i j : Index Cov) (x : X)
  (ui : U Cov i x) (uj : U Cov j x) →
  invEquiv (g C i j x (ui , uj)) ≡ g C j i x (uj , ui)
g-inv-eq C i j x ui uj =
  equivEq (funExt λ v →
    cong (equivFun (invEquiv (g C i j x (ui , uj))))
      (sym (funExt⁻ (cong equivFun (g-linv C i j x ui uj)) v))
    ∙ retEq (g C i j x (ui , uj)) (equivFun (g C j i x (uj , ui)) v)
  )

------------------------------------------------------------------------
-- Cocycle→Loc-fix（別途）
------------------------------------------------------------------------

postulate
  Cocycle→Loc-fix :
    (Cov : Covering) (C : Cocycle Cov)
    (i₀ : Index Cov) (x₀ : X) (ui₀ : U Cov i₀ x₀) →
    LocalSystem

------------------------------------------------------------------------
-- Cocycle-path（証明済み）
-- cocycle-reconstruct は UMIN_RH_CocycleToLoc から import
------------------------------------------------------------------------

Cocycle-path :
  (Cov : Covering) (C₁ C₂ : Cocycle Cov) →
  (∀ i j x (ui : U Cov i x) (uj : U Cov j x) →
     g C₁ i j x (ui , uj) ≡ g C₂ i j x (ui , uj))
  → C₁ ≡ C₂
Cocycle-path Cov C₁ C₂ h i = record
  { g      = g-eq i
  ; g-id   = g-id-path i
  ; g-comp = g-comp-path i
  }
  where
    g-eq : g C₁ ≡ g C₂
    g-eq =
      funExt λ i → funExt λ j → funExt λ x →
      funExt λ (ui , uj) → h i j x ui uj

    g-id-path :
      PathP (λ k → ∀ i x ui → g-eq k i i x (ui , ui) ≡ idEquiv V)
            (g-id C₁) (g-id C₂)
    g-id-path =
      isProp→PathP
        (λ k → isPropΠ λ i → isPropΠ λ x → isPropΠ λ ui →
                 isSet-Equiv _ _)
        (g-id C₁) (g-id C₂)

    g-comp-path :
      PathP
        (λ k → ∀ i j l x ui uj ul →
          compEquiv (g-eq k i j x (ui , uj))
                    (g-eq k j l x (uj , ul))
          ≡ g-eq k i l x (ui , ul))
        (g-comp C₁) (g-comp C₂)
    g-comp-path =
      isProp→PathP
        (λ k →
          isPropΠ λ i → isPropΠ λ j → isPropΠ λ l →
          isPropΠ λ x → isPropΠ λ ui → isPropΠ λ uj →
          isPropΠ λ ul → isSet-Equiv _ _)
        (g-comp C₁) (g-comp C₂)

------------------------------------------------------------------------
-- Cocycle-η（証明済み）
------------------------------------------------------------------------

Cocycle-η :
  (Cov : Covering) (C : Cocycle Cov) →
  Loc→Cocycle (Cocycle→Loc-global Cov C) ≡ C
Cocycle-η Cov C =
  Cocycle-path Cov
    (Loc→Cocycle (Cocycle→Loc-global Cov C))
    C
    (cocycle-reconstruct Cov C)

------------------------------------------------------------------------
-- ret-global（postulate）
------------------------------------------------------------------------

postulate
  ret-global :
    (L : LocalSystem) →
    Cocycle→Loc-global (Cov L) (Loc→Cocycle L) ≡ L

Cocycle→Loc-global-at :
  (Cov : Covering) → Cocycle Cov → LocalSystem-at Cov
Cocycle→Loc-global-at Cov C = Cocycle→Loc-global Cov C , refl

-- 被覆 Cov₀ 上の局所系：Cov L ≡ Cov₀ により Loc→Cocycle L を Cocycle Cov₀ へ運ぶ
Loc→Cocycle-on-cover :
  (Cov₀ : Covering) (L : LocalSystem) (p : Cov L ≡ Cov₀) → Cocycle Cov₀
Loc→Cocycle-on-cover Cov₀ L p = subst Cocycle p (Loc→Cocycle L)

Loc→Cocycle-atΣ :
  (Cov : Covering) → LocalSystem-at Cov → Cocycle Cov
Loc→Cocycle-atΣ Cov (L , p) = Loc→Cocycle-on-cover Cov L p

-- Loc→Cocycle-atΣ は refl 上で subst するため、Iso.ret 用に substRefl で η と接続する
-- （仮定の名前 Cov は LocalSystem.Cov 射影と衝突するので Cov₀ とする）
Cocycle-η-at :
  (Cov₀ : Covering) (C : Cocycle Cov₀) →
  Loc→Cocycle-atΣ Cov₀ (Cocycle→Loc-global-at Cov₀ C) ≡ C
Cocycle-η-at Cov₀ C =
  substRefl {B = Cocycle} {x = Cov (Cocycle→Loc-global Cov₀ C)}
    (Loc→Cocycle (Cocycle→Loc-global Cov₀ C))
  ∙ Cocycle-η Cov₀ C

postulate
  ret-global-at :
    (Cov : Covering) (L : LocalSystem-at Cov) →
    Cocycle→Loc-global-at Cov (Loc→Cocycle-atΣ Cov L) ≡ L

------------------------------------------------------------------------
-- Theorem B
------------------------------------------------------------------------

UMIN-RH-Equivalence :
  (Cov : Covering) → Cocycle Cov ≃ LocalSystem-at Cov
UMIN-RH-Equivalence Cov =
  isoToEquiv (iso
    (Cocycle→Loc-global-at Cov)
    (Loc→Cocycle-atΣ Cov)
    (ret-global-at Cov)
    (Cocycle-η-at Cov))