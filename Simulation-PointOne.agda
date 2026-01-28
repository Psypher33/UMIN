{-# OPTIONS --cubical --guardedness --no-import-sorts #-}

module UMIN.Simulation-PointOne where

open import UMIN.Grand-Unified-Protocol

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat renaming (zero to zeroℕ; suc to sucℕ)
open import Cubical.Data.Fin.Base using (Fin; fzero)
open import Cubical.Data.Fin.Properties using (discreteFin)
open import Cubical.Data.List using ([]; _∷_)
open import Cubical.Relation.Nullary using (yes; no)
open import Cubical.Data.Maybe using (just; nothing)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Bool using (Bool; true; false)

-- =============================================================================
-- [STEP 1] 1点宇宙の定義
-- =============================================================================

OnePoint : Type
OnePoint = Fin 1

SinglePointCauset : CausetStr OnePoint
SinglePointCauset = record
  { _<_    = λ _ _ → ⊥
  ; dist   = λ _ _ → zeroℝ
  ; irrefl = λ x x<x → x<x
  ; trans  = λ x y z x<y y<z → x<y
  ; dec-<  = λ x y → no (λ x<y → x<y)
  }

my-initial-universe : PhysicalUniverse
my-initial-universe = record
  { epoch        = zeroℕ
  ; carrier-type = OnePoint
  ; spacetime    = SinglePointCauset
  ; allPoints    = fzero ∷ []
  -- 【修正箇所】 fzero を取り除き、八元数そのものを渡します
  ; matter-field = λ _ → unitSuperOct 
  ; dark-sector  = λ _ → g-state initialTempℝ zeroℝ
  ; is-causal?   = λ _ _ → true
  ; dec-eq       = discreteFin {n = 1}
  }

-- =============================================================================
-- [STEP 2] 進化の実行
-- =============================================================================

Next-Universe : PhysicalUniverse
Next-Universe = EvolutionEngine.evolve my-initial-universe

Universe-at-137 : PhysicalUniverse
Universe-at-137 = EvolutionEngine.update-causality (record my-initial-universe { epoch = ETERNAL-137 })