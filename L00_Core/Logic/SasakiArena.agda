{-# OPTIONS --cubical --guardedness --safe #-}

module UMIN.L00_Core.Logic.SasakiArena where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)

open import UMIN.L00_Core.Axiom.TremblingCore
open import UMIN.L00_Core.Logic.SasakiCore

-- ============================================================
-- QuantumSasakiArena :
--   TremblingCore ＋ SasakiConn ＋ QuantumLattice を束ねる「場」
--   （まだ自動構成ではなく、「橋」のデータを明示するレコード）
-- ============================================================

record QuantumSasakiArena : Type₂ where
  field
    -- Trembling 側の一次元コア
    tc   : TremblingCore
    A    : Type
    conn : SasakiConn tc A

    -- 論理側の QuantumLattice
    L    : QuantumLattice

    -- A（物理状態）と L の命題格子との対応づけ
    --
    -- ここは設計の自由度が高いので、現時点では
    -- 「どう対応づけるか」をフィールドとして残す：
    --
    --   state-to-prop : 物理状態 a から命題（QProp L）への写像
    --   prop-to-state : 命題から代表状態への写像
    --
    state-to-prop : A → QuantumLattice.QProp L
    prop-to-state : QuantumLattice.QProp L → A

    -- 佐々木随伴と s, s† の対応付けの公理
    --
    -- Trembling 側の s, s† が、L 上の f_sasaki / g_sasaki
    -- （= SasakiOps）の随伴と整合することを表す「橋」。
    --
    sasaki-from-conn :
      let
        open QuantumLattice L
        open SasakiConn conn
        open SasakiOps L
      in
      ∀ (p : QuantumLattice.QProp L) (a : A)
      → (f_sasaki p (state-to-prop a) ≤ state-to-prop a)
      ≃ (state-to-prop a ≤ g_sasaki p (state-to-prop a))

  -- 便利のために、内部の構造を open しておく
  open TremblingCore tc public
  open SasakiConn  conn public
  open QuantumLattice L public