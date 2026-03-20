{-# OPTIONS --cubical --guardedness --no-import-sorts #-}

module UMIN.Simulation-TwoPoints where

open import UMIN.Grand-Unified-Protocol

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat 
  using (znots) 
  renaming (zero to zeroℕ; suc to sucℕ)
open import Cubical.Data.Fin.Base using (Fin; fzero; fsuc)
open import Cubical.Data.Fin.Properties using (discreteFin)
open import Cubical.Data.List using ([]; _∷_)
open import Cubical.Relation.Nullary using (Dec; yes; no)
open import Cubical.Data.Maybe using (just; nothing)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥; elim)
open import Cubical.Data.Bool using (Bool; true; false)

-- =============================================================================
-- [STEP 1] 2つの点を持つ宇宙
-- =============================================================================

TwoPoints : Type
TwoPoints = Fin 2

Point-A : TwoPoints
Point-A = fzero

Point-B : TwoPoints
Point-B = fsuc fzero

-- =============================================================================
-- [STEP 2] 因果構造の設計 (A -> B)
-- =============================================================================

data _<2_ : TwoPoints → TwoPoints → Type where
  A-leads-to-B : Point-A <2 Point-B

CausalStructure-2 : CausetStr TwoPoints
CausalStructure-2 = record
  { _<_    = _<2_
  ; dist   = λ x y → oneℝ
  ; irrefl = λ { x () }
  -- 【修正】推移律： A -> B はあるけれど、その先（B -> z）は絶対にないことを示します
  ; trans  = λ x y z → help x y z
  ; dec-<  = help-dec
  }
  where
    -- 推移律の不可能性証明
    help : ∀ x y z → x <2 y → y <2 z → x <2 z
    help .Point-A .Point-B z A-leads-to-B () -- B から始まる因果関係は定義されていないので () で通ります

    -- 因果判定の網羅的定義
    help-dec : (x y : TwoPoints) → Dec (x <2 y)
    help-dec (zeroℕ , _) (sucℕ zeroℕ , _) = yes A-leads-to-B
    help-dec (zeroℕ , _) (zeroℕ , _) = no (λ ())
    help-dec (sucℕ zeroℕ , _) (zeroℕ , _) = no (λ ())
    help-dec (sucℕ zeroℕ , _) (sucℕ zeroℕ , _) = no (λ ())

-- =============================================================================
-- [STEP 3] 2点宇宙の実装
-- =============================================================================

my-two-point-universe : PhysicalUniverse
my-two-point-universe = record
  { epoch        = zeroℕ
  ; carrier-type = TwoPoints
  ; spacetime    = CausalStructure-2
  ; allPoints    = Point-A ∷ Point-B ∷ []
  ; matter-field = λ _ → unitSuperOct
  ; dark-sector  = λ _ → g-state initialTempℝ zeroℝ
  ; is-causal?   = help-bool
  ; dec-eq       = discreteFin {n = 2}
  }
  where
    help-bool : TwoPoints → TwoPoints → Bool
    help-bool (zeroℕ , _) (sucℕ zeroℕ , _) = true
    help-bool _ _ = false

-- =============================================================================
-- [STEP 4] マグニチュードの計算
-- =============================================================================

module Calc = MagnitudeCalc my-two-point-universe

Universe-Magnitude : SuperOctonion
Universe-Magnitude = Calc.TotalMagnitudeSuperScalar.body (Universe-Magnitude fzero)