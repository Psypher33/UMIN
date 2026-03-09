{-# OPTIONS --cubical --guardedness --safe #-}

module UMIN.L00_Core.Logic.SasakiCore where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

-- =========================================================
-- 【形態 (Form)】: 宇宙の純粋構造 (The Pure Structure)
-- =========================================================

record QuantumLattice : Type₁ where
  field
    -- 1. 基底状態 (Carrier)
    QProp : Type
    
    -- 2. 因果律 (Causality / Partial Order)
    _≤_ : QProp → QProp → Type
    isProp≤ : ∀ x y → isProp (x ≤ y)

    -- 3. 根本演算 (Primitive Operations)
    perp : QProp → QProp             -- 否定
    meet : QProp → QProp → QProp     -- 共通
    join : QProp → QProp → QProp     -- 結合

    -- 4. 佐々木随伴公理 (The Sasaki Adjunction Axiom)
    -- ここには f_sasaki などの「名前」は登場させず、
    -- 純粋な「演算の構造」として双対性を刻印します。
    sasakiAdj :
      ∀ (p x y : QProp)
      → (meet p (join (perp p) x) ≤ y)      -- 射影測定 (Projected State)
      ≃ (x ≤ join (perp p) (meet p y))      -- 因果推論 (Inferred Cause)

-- =========================================================
-- 【変換コード (Transformation Code)】: 現象としての記述
-- =========================================================
-- 佐々木演算子は、構造（QuantumLattice）から導かれる「便利な語彙」として
-- レコードの外側（Module）で定義します。

module SasakiOps (L : QuantumLattice) where
  open QuantumLattice L

  -- 佐々木射影: 構造から導かれる「観測」という現象
  f_sasaki : QProp → QProp → QProp
  f_sasaki p x = meet p (join (perp p) x)

  -- 佐々木含意: 構造から導かれる「推論」という現象
  g_sasaki : QProp → QProp → QProp
  g_sasaki p y = join (perp p) (meet p y)

  -- 随伴性の再エイリアス (使いやすくするため)
  sasaki-duality : ∀ (p x y : QProp)
                 → (f_sasaki p x ≤ y) ≃ (x ≤ g_sasaki p y)
  sasaki-duality = sasakiAdj

-- （具体モデルは別モジュールで与える）
