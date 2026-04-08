{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- BG_FundamentalGroup.Axioms
-- 普遍被覆・encode/decode・ΩBG ≃ G は EM(G,1) の仕様レベルで postulate。
-- --safe な本体は親モジュール BG_FundamentalGroup.agda を参照。
-- ============================================================

module UMIN.L03_Func.QuantumKernel.BG_FundamentalGroup.Axioms where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import UMIN.L03_Func.QuantumKernel.BG_FundamentalGroup

postulate
  encode : {G : Group} → (base {G} ≡ base {G}) → Group.Carrier G

postulate
  encode-decode :
    (G : Group) (g : Group.Carrier G) →
    encode {G} (decode {G} g) ≡ g

  decode-encode :
    (G : Group) (p : base {G} ≡ base {G}) →
    decode {G} (encode {G} p) ≡ p

  ΩBG≃G :
    (G : Group) →
    (base {G} ≡ base {G}) ≃ Group.Carrier G
