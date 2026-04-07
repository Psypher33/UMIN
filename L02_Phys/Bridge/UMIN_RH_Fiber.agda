{-# OPTIONS --cubical --guardedness #-}
module UMIN.L02_Phys.Bridge.UMIN_RH_Fiber (X : Set₀) (V : Set₀) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels using (isOfHLevel→isOfHLevelDep)
open import Cubical.Data.Sigma

-- 第1層をインポート
open import UMIN.L01_Math.Geometry.UMIN_RH_Base X V

-- ==========================================
-- 5. Total Fiber (HITによる商空間構成)
-- ==========================================
data TotalFiber (Cov : Covering) (c : Cocycle Cov) (x : X) : Type₀ where
  base : (i : Index Cov) → U Cov i x → V → TotalFiber Cov c x
  paste : (i j : Index Cov) (ui : U Cov i x) (uj : U Cov j x) (v : V)
       → base i ui v ≡ base j uj (equivFun (g c i j x (ui , uj)) v)
  trunc : isSet (TotalFiber Cov c x)

TotalFiber-isSet : {Cov : Covering} {c : Cocycle Cov} {x : X} → isSet (TotalFiber Cov c x)
TotalFiber-isSet _ _ p q = trunc _ _ p q

-- ==========================================
-- TotalFiber の依存除去原理 (Custom Eliminator)
-- ==========================================
TotalFiber-elim :
  {Cov : Covering} {c : Cocycle Cov} {x : X}
  {P : TotalFiber Cov c x → Type₀}
  (pSet : (t : TotalFiber Cov c x) → isSet (P t))
  (fBase : (i : Index Cov) (ui : U Cov i x) (v : V) → P (base i ui v))
  (fPaste : (i j : Index Cov) (ui : U Cov i x) (uj : U Cov j x) (v : V)
          → PathP (λ k → P (paste i j ui uj v k))
                  (fBase i ui v)
                  (fBase j uj (equivFun (g c i j x (ui , uj)) v)))
  → (t : TotalFiber Cov c x) → P t
TotalFiber-elim {P = P} pSet fBase fPaste (base i ui v) = fBase i ui v
TotalFiber-elim {P = P} pSet fBase fPaste (paste i j ui uj v k) = fPaste i j ui uj v k
TotalFiber-elim {P = P} pSet fBase fPaste (trunc t1 t2 p q i j) =
  isOfHLevel→isOfHLevelDep 2 pSet
    (TotalFiber-elim pSet fBase fPaste t1)
    (TotalFiber-elim pSet fBase fPaste t2)
    (cong (TotalFiber-elim pSet fBase fPaste) p)
    (cong (TotalFiber-elim pSet fBase fPaste) q)
    (trunc t1 t2 p q) i j

-- ==========================================
-- 6. Loc → Cocycle の構成
-- ==========================================
Loc→Cocycle-g-id :
  (Cov : Covering) (L : LocalSystem) (i : Index Cov) (x : X) (ui : U Cov i x) →
  compEquiv (invEquiv (triv L Cov i x ui)) (triv L Cov i x ui) ≡ idEquiv V
Loc→Cocycle-g-id Cov L i x ui =
  equivEq (funExt (λ v → secEq (triv L Cov i x ui) v))

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