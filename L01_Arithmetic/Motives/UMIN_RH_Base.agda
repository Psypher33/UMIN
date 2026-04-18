{-# OPTIONS --cubical --guardedness --safe #-}

module UMIN.L01_Arithmetic.Motives.UMIN_RH_Base (X : Set₀) (V : Set₀) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

-- ==========================================
-- 1. 被覆
-- ==========================================

record Covering : Type₁ where
  field
    Index    : Type₀
    U        : Index → X → Type₀
    is-cover : (x : X) → ∥ Σ[ i ∈ Index ] U i x ∥₁

open Covering public

Overlap : {Cov : Covering} → Index Cov → Index Cov → X → Type₀
Overlap {Cov} i j x = U Cov i x × U Cov j x

-- ==========================================
-- 2. Cocycle（Čech 1-コサイクル）
-- ==========================================

record Cocycle (Cov : Covering) : Type₁ where
  field
    g      : (i j : Index Cov) (x : X)
           → Overlap {Cov} i j x → (V ≃ V)
    g-id   : (i : Index Cov) (x : X) (ui : U Cov i x)
           → g i i x (ui , ui) ≡ idEquiv V
    g-comp : (i j k : Index Cov) (x : X)
             (ui : U Cov i x) (uj : U Cov j x) (uk : U Cov k x)
           → compEquiv (g i j x (ui , uj)) (g j k x (uj , uk))
             ≡ g i k x (ui , uk)

open Cocycle public

-- ==========================================
-- 3. LocalSystem
-- descent data：F + triv のみ
-- compat は Loc→Cocycle で表現
-- ==========================================

record LocalSystem : Type₁ where
  field
    Cov   : Covering
    F     : X → Type₀
    F-set : (x : X) → isSet (F x)
    triv  : (i : Index Cov) (x : X) (ui : U Cov i x)
          → F x ≃ V

open LocalSystem public

-- ==========================================
-- 4. Loc→Cocycle
-- triv から Cocycle を作る（定義的）
-- ==========================================

Loc→Cocycle : (L : LocalSystem) → Cocycle (Cov L)
Loc→Cocycle L = record
  { g      = λ i j x (ui , uj) →
               compEquiv
                 (invEquiv (triv L i x ui))
                 (triv L j x uj)
  ; g-id   = λ i x ui →
               equivEq (funExt λ v →
                 secEq (triv L i x ui) v)
  ; g-comp = λ i j k x ui uj uk →
      let
        ti = triv L i x ui
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
  }

-- ==========================================
-- 5. LocalSystem-at（被覆固定版）
-- ==========================================

LocalSystem-at : Covering → Type₁
LocalSystem-at Cov₀ = Σ[ L ∈ LocalSystem ] (Cov L ≡ Cov₀)