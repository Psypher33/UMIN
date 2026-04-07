{-# OPTIONS --cubical --guardedness #-}
module UMIN.L02_Phys.Bridge.UMIN_RH_Core (X : Set₀) (V : Set₀) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isOfHLevel→isOfHLevelDep ; isOfHLevelPath')
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients
open import Cubical.HITs.PropositionalTruncation as PT

-- ==========================================
-- 1. 被覆とOverlap (被覆公理 is-cover を含む)
-- ==========================================
record Covering : Type₁ where
  field
    Index : Type₀
    U : Index → X → Type₀
    is-cover : (x : X) → ∥ (Σ[ i ∈ Index ] U i x) ∥₁

open Covering

Overlap : {Cov : Covering} → Index Cov → Index Cov → X → Type₀
Overlap {Cov} i j x = U Cov i x × U Cov j x

-- ==========================================
-- 2. Cocycle (Čech 1-cocycle)
-- ==========================================
record Cocycle (Cov : Covering) : Type₁ where
  field
    g : (i j : Index Cov) → (x : X) → Overlap {Cov} i j x → (V ≃ V)
    g-id : (i : Index Cov) (x : X) (ui : U Cov i x) → g i i x (ui , ui) ≡ idEquiv V
    g-comp : (i j k : Index Cov) (x : X) (ui : U Cov i x) (uj : U Cov j x) (uk : U Cov k x)
           → compEquiv (g i j x (ui , uj)) (g j k x (uj , uk)) ≡ g i k x (ui , uk)

open Cocycle

-- ==========================================
-- 3. Total Fiber (HITによる商空間構成)
-- ==========================================
data TotalFiber (Cov : Covering) (c : Cocycle Cov) (x : X) : Type₀ where
  base : (i : Index Cov) → U Cov i x → V → TotalFiber Cov c x
  paste : (i j : Index Cov) (ui : U Cov i x) (uj : U Cov j x) (v : V)
       → base i ui v ≡ base j uj (equivFun (g c i j x (ui , uj)) v)
  trunc : isSet (TotalFiber Cov c x)

-- trunc 面: 平行な二道 p q を同一視（SetTruncation の squash₂ と同じ役割）
TotalFiber-isSet : {Cov : Covering} {c : Cocycle Cov} {x : X} → isSet (TotalFiber Cov c x)
TotalFiber-isSet _ _ p q = trunc _ _ p q

-- ==========================================
-- 3.5. V 上のトルサー（各点のファイバー模型）
-- ==========================================
record VTorsor : Type₁ where
  field
    carrier : Type₀
    act : V → carrier → carrier
    transitive : (p q : carrier) → ∥ Σ[ v ∈ V ] act v p ≡ q ∥₁
    free : (v w : V) (p : carrier) → act v p ≡ act w p → v ≡ w

open VTorsor

-- ==========================================
-- 4. Local System (局所系)
-- ==========================================
record LocalSystem : Type₁ where
  field
    F : X → VTorsor
    transportF : {x y : X} → x ≡ y → carrier (F x) ≃ carrier (F y)
    triv : (Cov : Covering) → (i : Index Cov) → (x : X) → U Cov i x → carrier (F x) ≃ V

open LocalSystem

postulate
  carrier-isSet : {L : LocalSystem} {x : X} → isSet (carrier (F L x))

-- ==========================================
-- 5. Loc → Cocycle の構成
-- ==========================================
-- [✓] triv : carrier (F x) ≃ V なので invEquiv-is-linv は余域 V 側＝secEq（retEq ではない）
Loc→Cocycle-g-id :
  (Cov : Covering) (L : LocalSystem) (i : Index Cov) (x : X) (ui : U Cov i x) →
  compEquiv (invEquiv (triv L Cov i x ui)) (triv L Cov i x ui) ≡ idEquiv V
Loc→Cocycle-g-id Cov L i x ui =
  equivEq (funExt (λ v → secEq (triv L Cov i x ui) v))

-- [✓] compEquiv-assoc と invEquiv-is-rinv（carrier 側 retEq）で tj∘inv tj を相殺
Loc→Cocycle-g-comp :
  (Cov : Covering) (L : LocalSystem) (i j k : Index Cov) (x : X)
  (ui : U Cov i x) (uj : U Cov j x) (uk : U Cov k x) →
  let ti = triv L Cov i x ui
      tj = triv L Cov j x uj
      tk = triv L Cov k x uk
  in
  compEquiv (compEquiv (invEquiv ti) tj) (compEquiv (invEquiv tj) tk) ≡ compEquiv (invEquiv ti) tk
Loc→Cocycle-g-comp Cov L i j k x ui uj uk =
  let ti = triv L Cov i x ui
      tj = triv L Cov j x uj
      tk = triv L Cov k x uk
      middle : compEquiv tj (compEquiv (invEquiv tj) tk) ≡ tk
      middle =
          compEquiv-assoc tj (invEquiv tj) tk
        ∙ cong (λ e → compEquiv e tk) (invEquiv-is-rinv tj)
        ∙ compEquivIdEquiv tk
  in
    sym (compEquiv-assoc (invEquiv ti) tj (compEquiv (invEquiv tj) tk))
  ∙ cong (compEquiv (invEquiv ti)) middle

Loc→Cocycle : (Cov : Covering) → LocalSystem → Cocycle Cov
Loc→Cocycle Cov L = record
  { g = λ i j x (ui , uj) → compEquiv (invEquiv (triv L Cov i x ui)) (triv L Cov j x uj)
  ; g-id = λ i x ui → Loc→Cocycle-g-id Cov L i x ui
  ; g-comp = λ i j k x ui uj uk → Loc→Cocycle-g-comp Cov L i j k x ui uj uk
  }

-- ==========================================
-- 💥 6. 選択独立性補題 (Independence Lemma)
-- ==========================================
independence : {Cov : Covering} (L : LocalSystem) (x : X)
             (i j : Index Cov) (ui : U Cov i x) (uj : U Cov j x) (fx : carrier (F L x))
             → base i ui (equivFun (triv L Cov i x ui) fx) 
             ≡ base j uj (equivFun (triv L Cov j x uj) fx)
independence {Cov} L x i j ui uj fx =
  let 
    ti = triv L Cov i x ui
    tj = triv L Cov j x uj
    vi = equivFun ti fx
    gij = compEquiv (invEquiv ti) tj
    glue-path = paste {c = Loc→Cocycle Cov L} i j ui uj vi
    
    eval-path : equivFun gij vi ≡ equivFun tj fx
    eval-path = cong (equivFun tj) (retEq ti fx)
  in 
  glue-path ∙ cong (base j uj) eval-path

-- ==========================================
-- 💥 7–10. from / to / sec / ret / section-equiv
--        （abstract：from・to の実装をこのモジュール外に展開しない。
--         sec・ret はその展開に依存するため同じブロックに置く。）
-- ==========================================
abstract
  from : {Cov : Covering} {L : LocalSystem} {x : X}
       → carrier (F L x) → TotalFiber Cov (Loc→Cocycle Cov L) x
  from {Cov} {L} {x} fx =
    rec→Set (TotalFiber-isSet {Cov} {Loc→Cocycle Cov L} {x})
            (λ (i , ui) → base i ui (equivFun (triv L Cov i x ui) fx))
            (λ (i , ui) (j , uj) → independence L x i j ui uj fx)
            (is-cover Cov x)

  to : {Cov : Covering} {L : LocalSystem} {x : X}
     → TotalFiber Cov (Loc→Cocycle Cov L) x → carrier (F L x)
  to {Cov} {L} {x} (base i ui v) =
    equivFun (invEquiv (triv L Cov i x ui)) v

  to {Cov} {L} {x} (paste i j ui uj v k) =
    let
      ti = triv L Cov i x ui
      tj = triv L Cov j x uj
      gij-v = equivFun (compEquiv (invEquiv ti) tj) v
      glue-compat : equivFun (invEquiv ti) v ≡ equivFun (invEquiv tj) gij-v
      glue-compat = sym (retEq tj (equivFun (invEquiv ti) v))
    in
    glue-compat k

  to {Cov} {L} {x} (trunc t1 t2 p1 p2 k1 k2) =
    isOfHLevel→isOfHLevelDep 2 (λ _ → carrier-isSet {L = L} {x = x}) (to t1) (to t2) (cong to p1) (cong to p2)
      (trunc t1 t2 p1 p2) k1 k2

  -- sec / ret / section-equiv も同ブロック内：abstract 外では from/to が展開されないため
  sec : {Cov : Covering} {L : LocalSystem} {x : X} (fx : carrier (F L x))
      → to {Cov} {L} {x} (from {Cov} {L} {x} fx) ≡ fx
  sec {Cov} {L} {x} fx =
    PT.elim
      (λ _ → isOfHLevelPath' 1 carrier-isSet (to (from fx)) fx)
      (λ (i , ui) → retEq (triv L Cov i x ui) fx)
      (is-cover Cov x)

  ret : {Cov : Covering} {L : LocalSystem} {x : X} (t : TotalFiber Cov (Loc→Cocycle Cov L) x)
      → from {Cov} {L} {x} (to {Cov} {L} {x} t) ≡ t
  ret {Cov} {L} {x} (base i ui v) =
    PT.elim
      (λ _ → isOfHLevelPath' 1 TotalFiber-isSet (from (to (base i ui v))) (base i ui v))
      (λ (j , uj) →
        let
          ti   = triv L Cov i x ui
          tj   = triv L Cov j x uj
          fx   = equivFun (invEquiv ti) v

          step1 : equivFun ti fx ≡ v
          step1 = secEq ti v

          step2 : base j uj (equivFun tj fx) ≡ base i ui (equivFun ti fx)
          step2 = sym (independence L x i j ui uj fx)

          step3 : base i ui (equivFun ti fx) ≡ base i ui v
          step3 = cong (base i ui) step1
        in
        step2 ∙ step3)
      (is-cover Cov x)

  ret {Cov} {L} {x} (paste i j ui uj v k) =
    isOfHLevel→isOfHLevelDep 1
      (λ t → isOfHLevelPath' 1 TotalFiber-isSet (from (to t)) t)
      (ret (base i ui v))
      (ret (base j uj (equivFun (g (Loc→Cocycle Cov L) i j x (ui , uj)) v)))
      (paste i j ui uj v)
      k

  ret {Cov} {L} {x} (trunc t1 t2 p1 p2 k1 k2) =
    isOfHLevel→isOfHLevelDep 2
      (λ t → isProp→isSet (isOfHLevelPath' 1 TotalFiber-isSet (from (to t)) t))
      (ret t1) (ret t2)
      (cong ret p1)
      (cong ret p2)
      (trunc t1 t2 p1 p2) k1 k2

  section-equiv : (Cov : Covering) (L : LocalSystem) (x : X)
                → TotalFiber Cov (Loc→Cocycle Cov L) x ≃ carrier (F L x)
  section-equiv Cov L x =
    isoToEquiv (iso (to {Cov} {L} {x}) (from {Cov} {L} {x}) (sec {Cov} {L} {x}) (ret {Cov} {L} {x}))

-- ==========================================
-- Theorem B（別途）
-- ==========================================
postulate
  -- [P] Theorem B (Ext¹ ≃ LocalSystem) の宣言
  UMIN-RH-Equivalence : (Cov : Covering) → Cocycle Cov ≃ LocalSystem