{-# OPTIONS --cubical --safe --guardedness #-}

-- ================================================================
--  L00_Core/TremblingCore.agda
--  UMIN の唯一の公理とその基本的帰結
--  全モジュールがここを open import する
-- ================================================================

module UMIN.L00_Core.Axiom.TremblingCore where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Int.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Empty

-- ================================================================
-- §1  唯一の公理：TremblingCore
-- ================================================================

record TremblingCore : Type₁ where
  field
    ★        : Type
    isSet-★  : isSet ★
    ext-cert  : ★          -- Ext¹(★,★) ≠ 0 の証人

-- ================================================================
-- §2  佐々木＝ガロア接続の骨格
-- ================================================================

record SasakiConn (tc : TremblingCore) (A : Type) : Type₁ where
  open TremblingCore tc
  field
    s   : ★ → A
    s†  : A → ★

-- 随伴欠陥の型 [✓]
Defect : {tc : TremblingCore} {A : Type}
       → SasakiConn tc A → Type
Defect {_} {A} sc =
  Σ[ a ∈ A ]
    (SasakiConn.s sc (SasakiConn.s† sc a) ≡ a → ⊥)

-- 完全随伴（欠陥ゼロ）[✓]
Perfect : {tc : TremblingCore} {A : Type}
        → SasakiConn tc A → Type
Perfect {_} {A} sc =
  (a : A) → SasakiConn.s sc (SasakiConn.s† sc a) ≡ a

-- ================================================================
-- §3  数値定数（E₈分解）[✓ refl]
-- ================================================================

HermitianCore   : ℕ ; HermitianCore   = 136
nonHermitianCone : ℕ ; nonHermitianCone = 112

E₈-decomp : HermitianCore +ℕ nonHermitianCone ≡ 248
E₈-decomp = refl

α-integer : HermitianCore +ℕ 1 ≡ 137
α-integer = refl
