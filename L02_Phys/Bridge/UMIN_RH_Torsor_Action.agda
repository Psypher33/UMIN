{-# OPTIONS --cubical --guardedness #-}
module UMIN.L02_Phys.Bridge.UMIN_RH_Torsor_Action (X : Set₀) (V : Set₀) where

open import UMIN.L02_Phys.Bridge.UMIN_RH_Core X V
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels using (isOfHLevel→isOfHLevelDep)

open Covering
open Cocycle

-- ==========================================
-- 1. V上の群作用と同変性の公理化
-- ==========================================
postulate
  -- V を群（あるいは加群）として扱い、作用 addV を定義
  addV : V → V → V

  -- コサイクル g_ij は「V 上の同型」なので、V の作用と可換（同変）
  g-equivariance :
    {Cov : Covering} (c : Cocycle Cov) (i j : Index Cov) (x : X) (ov : Overlap {Cov} i j x)
    (v v' : V) →
    equivFun (g c i j x ov) (addV v v') ≡ addV (equivFun (g c i j x ov) v) v'

-- ==========================================
-- 2. TotalFiber への V の作用 act-fiber
-- ==========================================
act-fiber :
  {Cov : Covering} {c : Cocycle Cov} {x : X} →
  V → TotalFiber Cov c x → TotalFiber Cov c x

-- ① base：ファイバー内の座標 v に v' を加える
act-fiber v' (base i ui v) = base i ui (addV v v')

-- ② paste：同変性で paste セルと整合する経路を構成
act-fiber {Cov} {c} {x} v' (paste i j ui uj v k) =
  let
    equiv-path = g-equivariance c i j x (ui , uj) v v'
    step1 = paste i j ui uj (addV v v')
    step2 :
      base j uj (equivFun (g c i j x (ui , uj)) (addV v v'))
      ≡ base j uj (addV (equivFun (g c i j x (ui , uj)) v) v')
    step2 = cong (base j uj) equiv-path
  in
  (step1 ∙ step2) k

-- ③ trunc：ターゲットが集合なので isOfHLevel→isOfHLevelDep で送る
act-fiber {Cov} {c} {x} v' (trunc t1 t2 p1 p2 k1 k2) =
  isOfHLevel→isOfHLevelDep 2 (λ _ → TotalFiber-isSet {Cov = Cov} {c = c} {x = x})
    (act-fiber v' t1) (act-fiber v' t2)
    (cong (act-fiber v') p1) (cong (act-fiber v') p2)
    (trunc t1 t2 p1 p2) k1 k2
