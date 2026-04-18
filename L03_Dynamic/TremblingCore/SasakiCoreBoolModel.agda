{-# OPTIONS --cubical --guardedness --safe #-}

-- ============================================================
-- UMIN.L03_Dynamic.TremblingCore.SasakiCoreBoolModel
-- 
-- [✓] Action 1 完了: BoolSasakiAdj の postulate を削除
--     全8ケースの場合分けで証明 → --safe フラグ追加
-- ============================================================

module UMIN.L03_Dynamic.TremblingCore.SasakiCoreBoolModel where

-- Cubical.Core.Everything は cubical に無い。Prelude が Core を含む。
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Data.Bool using (Bool; true; false; not; _and_; _or_)
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Unit

open import UMIN.L00_Foundation.Logic.SasakiCore

-- ============================================================
-- Bool 上の順序定義
-- ============================================================

Bool≤ : Bool → Bool → Type
Bool≤ false _    = Unit
Bool≤ true  true = Unit
Bool≤ true  false = ⊥

isPropBool≤ : ∀ x y → isProp (Bool≤ x y)
isPropBool≤ false _     = isPropUnit
isPropBool≤ true  true  = isPropUnit
isPropBool≤ true  false = isProp⊥

-- ============================================================
-- [✓] BoolSasakiAdj：全8ケース場合分けで証明（postulate ゼロ）
--
-- 命題: Bool≤ (p ∧ (¬p ∨ x)) y  ≃  Bool≤ x (¬p ∨ (p ∧ y))
--
-- 証明方針:
--   Bool は有限（2値）なので p,x,y の全8ケースを網羅する。
--   各ケースで LHS/RHS が Unit か ⊥ に簡約され、
--   isContrUnit / isProp⊥ から ≃ が自動的に構成される。
--
-- ケース表:
--   p=F x=F y=F : Unit ≃ Unit  [idEquiv Unit]
--   p=F x=F y=T : Unit ≃ Unit  [idEquiv Unit]
--   p=F x=T y=F : Unit ≃ Unit  [idEquiv Unit]
--   p=F x=T y=T : Unit ≃ Unit  [idEquiv Unit]
--   p=T x=F y=F : Unit ≃ Unit  [idEquiv Unit]
--   p=T x=F y=T : Unit ≃ Unit  [idEquiv Unit]
--   p=T x=T y=F : ⊥   ≃ ⊥     [idEquiv ⊥]
--   p=T x=T y=T : Unit ≃ Unit  [idEquiv Unit]
-- ============================================================

BoolSasakiAdj :
  ∀ (p x y : Bool)
  → Bool≤ (p and (not p or x)) y
  ≃ Bool≤ x (not p or p and y)
-- p = false branch: LHS = Bool≤ (false ∧ ...) y = Bool≤ false y = Unit
--                   RHS = Bool≤ x (true ∨ ...)  = Bool≤ x true
BoolSasakiAdj false false y = idEquiv Unit
BoolSasakiAdj false true  y = idEquiv Unit
-- p = true branch
-- not p = false, so:
--   LHS arg: true ∧ (false ∨ x) = x
--   RHS arg: false ∨ (true ∧ y) = y
BoolSasakiAdj true false false = idEquiv Unit  -- Bool≤ false false = Unit ≃ Bool≤ false false = Unit
BoolSasakiAdj true false true  = idEquiv Unit  -- Bool≤ false true  = Unit ≃ Bool≤ false true  = Unit
BoolSasakiAdj true true  false = idEquiv ⊥     -- Bool≤ true  false = ⊥   ≃ Bool≤ true  false = ⊥
BoolSasakiAdj true true  true  = idEquiv Unit  -- Bool≤ true  true  = Unit ≃ Bool≤ true  true  = Unit

-- ============================================================
-- [✓] BoolLattice：--safe 対応の具体モデル
-- ============================================================

BoolLattice : QuantumLattice
BoolLattice = record
  { QProp     = Bool
  ; _≤_       = Bool≤
  ; isProp≤   = isPropBool≤
  ; perp      = not
  ; meet      = _and_
  ; join      = _or_
  ; sasakiAdj = λ p x y → BoolSasakiAdj p x y
  }

-- ============================================================
-- [✓] 健全性確認：BoolLattice が QuantumLattice の instance
--     SasakiCore の公理系が Bool で反駁不能であることを示す
-- ============================================================

_ : QuantumLattice
_ = BoolLattice