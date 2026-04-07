{-# OPTIONS --cubical --guardedness #-}
module UMIN.L01_Math.Geometry.UMIN_RH_Base (X : Set₀) (V : Set₀) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

-- ==========================================
-- 1. 被覆とOverlap
-- ==========================================
record Covering : Type₁ where
  field
    Index : Type₀
    U : Index → X → Type₀
    is-cover : (x : X) → ∥ (Σ[ i ∈ Index ] U i x) ∥₁

open Covering public

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

open Cocycle public

-- ==========================================
-- 3. V 上のトルサー
-- ==========================================
record VTorsor : Type₁ where
  field
    carrier : Type₀
    act : V → carrier → carrier
    transitive : (p q : carrier) → ∥ Σ[ v ∈ V ] act v p ≡ q ∥₁
    free : (v w : V) (p : carrier) → act v p ≡ act w p → v ≡ w

open VTorsor public

-- ==========================================
-- 4. Local System (局所系)
-- ==========================================
record LocalSystem : Type₁ where
  field
    F : X → VTorsor
    transportF : {x y : X} → x ≡ y → carrier (F x) ≃ carrier (F y)
    triv : (Cov : Covering) → (i : Index Cov) → (x : X) → U Cov i x → carrier (F x) ≃ V

open LocalSystem public

postulate
  carrier-isSet : {L : LocalSystem} {x : X} → isSet (carrier (F L x))