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
    carrier-isSet : isSet carrier
    act : V → carrier → carrier
    transitive : (p q : carrier) → ∥ Σ[ v ∈ V ] act v p ≡ q ∥₁
    free : (v w : V) (p : carrier) → act v p ≡ act w p → v ≡ w

open VTorsor

-- ==========================================
-- 4. Local System (局所系)
-- ==========================================
record LocalSystem : Type₁ where
  field
    Cov : Covering
    F : X → VTorsor
    transportF : {x y : X} → x ≡ y → carrier (F x) ≃ carrier (F y)
    triv : (i : Index Cov) → (x : X) → U Cov i x → carrier (F x) ≃ V

open LocalSystem

LocalSystem-at : Covering → Type₁
LocalSystem-at Cov₀ = Σ[ L ∈ LocalSystem ] (Cov L ≡ Cov₀)

-- ==========================================
-- 5. Loc → Cocycle の構成
-- ==========================================
-- [✓] triv : carrier (F x) ≃ V なので invEquiv-is-linv は余域 V 側＝secEq（retEq ではない）
Loc→Cocycle-g-id :
  (L : LocalSystem) (i : Index (Cov L)) (x : X) (ui : U (Cov L) i x) →
  compEquiv (invEquiv (triv L i x ui)) (triv L i x ui) ≡ idEquiv V
Loc→Cocycle-g-id L i x ui =
  equivEq (funExt (λ v → secEq (triv L i x ui) v))

-- [✓] compEquiv-assoc と invEquiv-is-rinv（carrier 側 retEq）で tj∘inv tj を相殺
Loc→Cocycle-g-comp :
  (L : LocalSystem) (i j k : Index (Cov L)) (x : X)
  (ui : U (Cov L) i x) (uj : U (Cov L) j x) (uk : U (Cov L) k x) →
  let ti = triv L i x ui
      tj = triv L j x uj
      tk = triv L k x uk
  in
  compEquiv (compEquiv (invEquiv ti) tj) (compEquiv (invEquiv tj) tk) ≡ compEquiv (invEquiv ti) tk
Loc→Cocycle-g-comp L i j k x ui uj uk =
  let ti = triv L i x ui
      tj = triv L j x uj
      tk = triv L k x uk
      middle : compEquiv tj (compEquiv (invEquiv tj) tk) ≡ tk
      middle =
          compEquiv-assoc tj (invEquiv tj) tk
        ∙ cong (λ e → compEquiv e tk) (invEquiv-is-rinv tj)
        ∙ compEquivIdEquiv tk
  in
    sym (compEquiv-assoc (invEquiv ti) tj (compEquiv (invEquiv tj) tk))
  ∙ cong (compEquiv (invEquiv ti)) middle

Loc→Cocycle : (L : LocalSystem) → Cocycle (Cov L)
Loc→Cocycle L = record
  { g = λ i j x (ui , uj) → compEquiv (invEquiv (triv L i x ui)) (triv L j x uj)
  ; g-id = λ i x ui → Loc→Cocycle-g-id L i x ui
  ; g-comp = λ i j k x ui uj uk → Loc→Cocycle-g-comp L i j k x ui uj uk
  }

-- ==========================================
-- 💥 6. 選択独立性補題 (Independence Lemma)
-- ==========================================
independence : (L : LocalSystem) (x : X)
             (i j : Index (Cov L)) (ui : U (Cov L) i x) (uj : U (Cov L) j x) (fx : carrier (F L x))
             → base i ui (equivFun (triv L i x ui) fx) 
             ≡ base j uj (equivFun (triv L j x uj) fx)
independence L x i j ui uj fx =
  let 
    ti = triv L i x ui
    tj = triv L j x uj
    vi = equivFun ti fx
    gij = compEquiv (invEquiv ti) tj
    glue-path = paste {c = Loc→Cocycle L} i j ui uj vi
    
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
  from : {L : LocalSystem} {x : X}
       → carrier (F L x) → TotalFiber (Cov L) (Loc→Cocycle L) x
  from {L} {x} fx =
    rec→Set (TotalFiber-isSet {Cov = Cov L} {c = Loc→Cocycle L} {x = x})
            (λ (i , ui) → base i ui (equivFun (triv L i x ui) fx))
            (λ (i , ui) (j , uj) → independence L x i j ui uj fx)
            (is-cover (Cov L) x)

  to : {L : LocalSystem} {x : X}
     → TotalFiber (Cov L) (Loc→Cocycle L) x → carrier (F L x)
  to {L} {x} (base i ui v) =
    equivFun (invEquiv (triv L i x ui)) v

  to {L} {x} (paste i j ui uj v k) =
    let
      ti = triv L i x ui
      tj = triv L j x uj
      gij-v = equivFun (compEquiv (invEquiv ti) tj) v
      glue-compat : equivFun (invEquiv ti) v ≡ equivFun (invEquiv tj) gij-v
      glue-compat = sym (retEq tj (equivFun (invEquiv ti) v))
    in
    glue-compat k

  to {L} {x} (trunc t1 t2 p1 p2 k1 k2) =
    isOfHLevel→isOfHLevelDep 2 (λ _ → carrier-isSet (F L x)) (to t1) (to t2) (cong to p1) (cong to p2)
      (trunc t1 t2 p1 p2) k1 k2

  -- sec / ret / section-equiv も同ブロック内：abstract 外では from/to が展開されないため
  sec : {L : LocalSystem} {x : X} (fx : carrier (F L x))
      → to {L} {x} (from {L} {x} fx) ≡ fx
  sec {L} {x} fx =
    PT.elim
      (λ _ → isOfHLevelPath' 1 (carrier-isSet (F L x)) (to (from fx)) fx)
      (λ (i , ui) → retEq (triv L i x ui) fx)
      (is-cover (Cov L) x)

  ret : {L : LocalSystem} {x : X} (t : TotalFiber (Cov L) (Loc→Cocycle L) x)
      → from {L} {x} (to {L} {x} t) ≡ t
  ret {L} {x} (base i ui v) =
    PT.elim
      (λ _ → isOfHLevelPath' 1 TotalFiber-isSet (from (to (base i ui v))) (base i ui v))
      (λ (j , uj) →
        let
          ti   = triv L i x ui
          tj   = triv L j x uj
          fx   = equivFun (invEquiv ti) v

          step1 : equivFun ti fx ≡ v
          step1 = secEq ti v

          step2 : base j uj (equivFun tj fx) ≡ base i ui (equivFun ti fx)
          step2 = sym (independence L x i j ui uj fx)

          step3 : base i ui (equivFun ti fx) ≡ base i ui v
          step3 = cong (base i ui) step1
        in
        step2 ∙ step3)
      (is-cover (Cov L) x)

  ret {L} {x} (paste i j ui uj v k) =
    isOfHLevel→isOfHLevelDep 1
      (λ t → isOfHLevelPath' 1 TotalFiber-isSet (from (to t)) t)
      (ret (base i ui v))
      (ret (base j uj (equivFun (g (Loc→Cocycle L) i j x (ui , uj)) v)))
      (paste i j ui uj v)
      k

  ret {L} {x} (trunc t1 t2 p1 p2 k1 k2) =
    isOfHLevel→isOfHLevelDep 2
      (λ t → isProp→isSet (isOfHLevelPath' 1 TotalFiber-isSet (from (to t)) t))
      (ret t1) (ret t2)
      (cong ret p1)
      (cong ret p2)
      (trunc t1 t2 p1 p2) k1 k2

  section-equiv : (L : LocalSystem) (x : X)
                → TotalFiber (Cov L) (Loc→Cocycle L) x ≃ carrier (F L x)
  section-equiv L x =
    isoToEquiv (iso (to {L} {x}) (from {L} {x}) (sec {L} {x}) (ret {L} {x}))

-- ==========================================
-- Theorem B（別途）
-- ==========================================
postulate
  -- [P] Theorem B（固定被覆上の局所系とコサイクルの同値）
  UMIN-RH-Equivalence : (Cov : Covering) → Cocycle Cov ≃ LocalSystem-at Cov