{-# OPTIONS --cubical --guardedness #-}
module UMIN.L02_Phys.Bridge.UMIN_RH_Lemma (X : Set₀) (V : Set₀) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma

-- 第1層と第2層をインポート
open import UMIN.L01_Math.Geometry.UMIN_RH_Base X V
open import UMIN.L02_Phys.Bridge.UMIN_RH_Fiber X V

-- ==========================================
-- 6. 選択独立性補題 (Independence Lemma)
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