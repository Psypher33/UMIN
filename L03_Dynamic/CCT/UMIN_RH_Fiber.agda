{-# OPTIONS --cubical --guardedness --safe #-}

module UMIN.L03_Dynamic.CCT.UMIN_RH_Fiber (X : Set₀) (V : Set₀) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels using (isOfHLevel→isOfHLevelDep)
open import Cubical.Data.Sigma

open import UMIN.L01_Arithmetic.Motives.UMIN_RH_Base X V

-- ==========================================
-- 5. Total Fiber（HIT による商空間構成）
-- ==========================================

data TotalFiber (Cov : Covering) (c : Cocycle Cov) (x : X) : Type₀ where
  base  : (i : Index Cov) → U Cov i x → V → TotalFiber Cov c x
  paste : (i j : Index Cov) (ui : U Cov i x) (uj : U Cov j x) (v : V)
        → base i ui v
          ≡ base j uj (equivFun (g c i j x (ui , uj)) v)
  trunc : isSet (TotalFiber Cov c x)

TotalFiber-isSet :
  {Cov : Covering} {c : Cocycle Cov} {x : X} →
  isSet (TotalFiber Cov c x)
TotalFiber-isSet _ _ p q = trunc _ _ p q

-- ==========================================
-- TotalFiber の依存除去原理
-- ==========================================

TotalFiber-elim :
  {Cov : Covering} {c : Cocycle Cov} {x : X}
  {P : TotalFiber Cov c x → Type₀}
  (pSet   : (t : TotalFiber Cov c x) → isSet (P t))
  (fBase  : (i : Index Cov) (ui : U Cov i x) (v : V)
          → P (base i ui v))
  (fPaste : (i j : Index Cov) (ui : U Cov i x) (uj : U Cov j x) (v : V)
          → PathP (λ k → P (paste i j ui uj v k))
                  (fBase i ui v)
                  (fBase j uj (equivFun (g c i j x (ui , uj)) v)))
  → (t : TotalFiber Cov c x) → P t
TotalFiber-elim pSet fBase fPaste (base i ui v)   = fBase i ui v
TotalFiber-elim pSet fBase fPaste (paste i j ui uj v k) =
  fPaste i j ui uj v k
TotalFiber-elim {P = P} pSet fBase fPaste (trunc t1 t2 p q i j) =
  isOfHLevel→isOfHLevelDep 2 pSet
    (TotalFiber-elim pSet fBase fPaste t1)
    (TotalFiber-elim pSet fBase fPaste t2)
    (cong (TotalFiber-elim pSet fBase fPaste) p)
    (cong (TotalFiber-elim pSet fBase fPaste) q)
    (trunc t1 t2 p q) i j

-- ==========================================
-- Loc→Cocycle は Base に移動済み
-- ここでは再 export のみ
-- ==========================================

-- Loc→Cocycle : LocalSystem → Cocycle (Cov L)
-- は UMIN_RH_Base から import 済み