{-# OPTIONS --cubical --guardedness #-}

open import Cubical.Foundations.Prelude

module UMIN.L02_Phys.RH.TheoremB (X : Set₀) (V : Set₀)
  (isSetV : isSet V) where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
  using (isPropΠ ; isSetΣ ; isSet→ ; isPropIsSet)
open import Cubical.Foundations.Isomorphism
  using (Iso ; iso ; isoToEquiv)
open import Cubical.Foundations.Univalence
  using (ua ; uaIdEquiv ; ua-unglue)
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties using (ΣPathPProp)
open import Cubical.HITs.PropositionalTruncation as PT

open import UMIN.L01_Math.RH.Base X V
open import UMIN.L02_Phys.RH.Fiber X V
open import UMIN.L02_Phys.RH.TotalFiberTriv X V isSetV
open import UMIN.L02_Phys.RH.Equiv_Final X V
open import UMIN.L02_Phys.RH.CocycleToLoc X V isSetV

------------------------------------------------------------------------
-- ① isSet-Equiv
------------------------------------------------------------------------

isSet-Equiv : isSet (V ≃ V)
isSet-Equiv =
  isSetΣ
    (isSet→ isSetV)
    (λ f → isProp→isSet (isPropIsEquiv f))

------------------------------------------------------------------------
-- ② Cocycle-path
-- g が pointwise 等しければ Cocycle 全体が等しい
------------------------------------------------------------------------

Cocycle-path :
  (Cov : Covering) (C₁ C₂ : Cocycle Cov) →
  (∀ i j x (ui : U Cov i x) (uj : U Cov j x) →
     g C₁ i j x (ui , uj) ≡ g C₂ i j x (ui , uj))
  → C₁ ≡ C₂
Cocycle-path Cov C₁ C₂ h k = record
  { g      = g-eq k
  ; g-id   = g-id-path k
  ; g-comp = g-comp-path k
  }
  where
    g-eq : g C₁ ≡ g C₂
    g-eq =
      funExt λ i → funExt λ j → funExt λ x →
      funExt λ (ui , uj) → h i j x ui uj

    g-id-path :
      PathP
        (λ k → ∀ i x ui → g-eq k i i x (ui , ui) ≡ idEquiv V)
        (g-id C₁) (g-id C₂)
    g-id-path =
      isProp→PathP
        (λ k →
          isPropΠ λ i → isPropΠ λ x → isPropΠ λ ui →
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
-- ③ Cocycle-η
-- Loc→Cocycle (Cocycle→Loc-global C) ≡ C
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
-- ④ LocalSystem-≡
-- F + F-set + triv の等式から LocalSystem 全体の等式へ
------------------------------------------------------------------------

LocalSystem-≡ :
  {L₁ L₂ : LocalSystem}
  → (cov-eq  : Cov L₁ ≡ Cov L₂)
  → (F-eq    : ∀ x → L₁ .F x ≡ L₂ .F x)
  → (triv-eq :
      PathP
        (λ k →
          (i : Index (cov-eq k)) (x : X) (ui : U (cov-eq k) i x)
          → F-eq x k ≃ V)
        (triv L₁) (triv L₂))
  → L₁ ≡ L₂
LocalSystem-≡ {L₁} {L₂} cov-eq F-eq triv-eq k = record
  { Cov   = cov-eq k
  ; F     = λ x → F-eq x k
  ; F-set = λ x →
      isProp→PathP
        (λ k' → isPropIsSet {A = F-eq x k'})
        (F-set L₁ x) (F-set L₂ x) k
  ; triv  = λ i x ui → triv-eq k i x ui
  }

------------------------------------------------------------------------
-- ⑤ ret-global
-- Cocycle→Loc-global (Loc→Cocycle L) ≡ L
------------------------------------------------------------------------

private
  -- compEquiv の関数成分（.fst の合成）
  equivFun-compEquiv∘ :
    {A B C : Type₀} (f : A ≃ B) (g : B ≃ C) (a : A) →
    equivFun (compEquiv f g) a ≡ equivFun g (equivFun f a)
  equivFun-compEquiv∘ f g a = refl

  -- TotalFiber-triv は isoToEquiv で forward = TotalFiber-to-V
  equivFun-TotalFiber-triv :
    {Cov : Covering} {C : Cocycle Cov} {x : X}
    (i : Index Cov) (ui : U Cov i x) (t : TotalFiber Cov C x) →
    equivFun (TotalFiber-triv i ui) t ≡ TotalFiber-to-V i ui t
  equivFun-TotalFiber-triv i ui t = refl

  -- base 上：compEquiv section-equiv triv → ti ∘ to → ti ∘ invEq tj → g j i → TotalFiber-to-V
  compEquiv-section-equiv-on-base :
    (L : LocalSystem) (x : X) (i : Index (Cov L)) (ui : U (Cov L) i x)
    (j : Index (Cov L)) (uj : U (Cov L) j x) (v : V) →
    equivFun (compEquiv (section-equiv {L = L} {x = x}) (triv L i x ui)) (base j uj v)
    ≡ equivFun (TotalFiber-triv {Cov = Cov L} {C = Loc→Cocycle L} {x = x} i ui) (base j uj v)
  compEquiv-section-equiv-on-base L x i ui j uj v =
    let
      ti = triv L i x ui
      tj = triv L j x uj
      sec = section-equiv {L = L} {x = x}
      -- invEquiv の向き：Iso.fun (invIso …) ≡ invEq
      invEq≡equivFun-invEquiv : invEq tj v ≡ equivFun (invEquiv tj) v
      invEq≡equivFun-invEquiv = refl
    in
      equivFun-compEquiv∘ sec ti (base j uj v)
    ∙ cong (equivFun ti) invEq≡equivFun-invEquiv
    ∙ sym (equivFun-compEquiv∘ (invEquiv tj) ti v)
    ∙ sym
        (equivFun-TotalFiber-triv {Cov = Cov L} {C = Loc→Cocycle L} {x = x} i ui
          (base {Cov = Cov L} {c = Loc→Cocycle L} {x = x} j uj v))

-- section-equiv 後に triv を合成すると TotalFiber-triv と一致
compEquiv-section-equiv-triv≡TotalFiber-triv :
  (L : LocalSystem) (x : X)
  (i : Index (Cov L)) (ui : U (Cov L) i x) →
  compEquiv (section-equiv {L = L} {x = x}) (triv L i x ui)
  ≡ TotalFiber-triv {Cov = Cov L} {C = Loc→Cocycle L} {x = x} i ui
compEquiv-section-equiv-triv≡TotalFiber-triv L x i ui =
  equivEq
    (funExt
      (TotalFiber-elim
        (λ t →
          isProp→isSet
            (isSetV
              (equivFun (compEquiv (section-equiv {L = L} {x = x}) (triv L i x ui)) t)
              (equivFun
                (TotalFiber-triv {Cov = Cov L} {C = Loc→Cocycle L} {x = x} i ui)
                t)))
        (λ j uj v → compEquiv-section-equiv-on-base L x i ui j uj v)
        (λ j j' uj uj' v k →
          isProp→PathP
            (λ k' →
              isSetV
                (equivFun
                  (compEquiv (section-equiv {L = L} {x = x}) (triv L i x ui))
                  (paste j j' uj uj' v k'))
                (equivFun
                  (TotalFiber-triv {Cov = Cov L} {C = Loc→Cocycle L} {x = x} i ui)
                  (paste j j' uj uj' v k')))
            (compEquiv-section-equiv-on-base L x i ui j uj v)
            (compEquiv-section-equiv-on-base L x i ui j' uj'
              (equivFun (g (Loc→Cocycle L) j j' x (uj , uj')) v))
            k)))

ret-global :
  (L : LocalSystem) →
  Cocycle→Loc-global (Cov L) (Loc→Cocycle L) ≡ L
ret-global L =
  LocalSystem-≡
    -- cov-eq：Cov は同じ
    refl
    -- F-eq：TotalFiber (Cov L) (Loc→Cocycle L) x ≡ F L x
    (λ x → ua (section-equiv {L = L} {x = x}))
    -- triv-eq：equivPathP（ua-unglue ⊗ triv）で isEquiv 端点を調整し、subst で TotalFiber-triv に合わせる
    (λ k i x ui →
      (subst
        (λ e →
          PathP
            (λ j → (ua (section-equiv {L = L} {x = x}) j ≃ V))
            e
            (triv L i x ui))
        (compEquiv-section-equiv-triv≡TotalFiber-triv L x i ui)
        (equivPathP {e = compEquiv (section-equiv {L = L} {x = x}) (triv L i x ui)}
          {f = triv L i x ui}
          (λ j t →
            equivFun (triv L i x ui) (ua-unglue (section-equiv {L = L} {x = x}) j t))))
      k)
------------------------------------------------------------------------
-- ⑥ UMIN-RH-Equivalence：最終実装
------------------------------------------------------------------------

UMIN-RH-Equivalence :
  (isSetCov : isSet Covering) (Cov₀ : Covering) →
  Cocycle Cov₀ ≃ LocalSystem-at Cov₀
UMIN-RH-Equivalence isSetCov Cov₀ =
  isoToEquiv (iso to' from' sec' ret')
  where
    to' : Cocycle Cov₀ → LocalSystem-at Cov₀
    to' C = Cocycle→Loc-global Cov₀ C , refl

    from' : LocalSystem-at Cov₀ → Cocycle Cov₀
    from' (L , p) = subst Cocycle p (Loc→Cocycle L)

    ret' : (C : Cocycle Cov₀) → from' (to' C) ≡ C
    ret' C =
      substRefl {B = Cocycle} (Loc→Cocycle (Cocycle→Loc-global Cov₀ C))
      ∙ Cocycle-η Cov₀ C

    sec'-fst-path :
      (L : LocalSystem) (p : Cov L ≡ Cov₀) →
      Cocycle→Loc-global Cov₀ (subst Cocycle p (Loc→Cocycle L)) ≡ L
    sec'-fst-path L p =
      J
        (λ Cov₁ q →
          Cocycle→Loc-global Cov₁ (subst Cocycle q (Loc→Cocycle L)) ≡ L)
        ( cong (Cocycle→Loc-global (Cov L))
            (substRefl {B = Cocycle} (Loc→Cocycle L))
        ∙ ret-global L)
        p

    sec' : (La : LocalSystem-at Cov₀) → to' (from' La) ≡ La
    sec' (L , p) =
      ΣPathPProp
        {A = λ _ → LocalSystem}
        {B = λ _ L₁ → Cov L₁ ≡ Cov₀}
        {u =
          ( Cocycle→Loc-global Cov₀ (subst Cocycle p (Loc→Cocycle L))
          , refl
          )}
        {v = (L , p)}
        (λ L₁ → isSetCov (Cov L₁) Cov₀)
        (sec'-fst-path L p)