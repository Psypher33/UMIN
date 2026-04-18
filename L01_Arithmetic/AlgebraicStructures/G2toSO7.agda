{-# OPTIONS --cubical --guardedness --safe #-}

module UMIN.L01_Arithmetic.AlgebraicStructures.G2toSO7 where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

-- ================================================================
-- 1. 公理を record で受け取る（postulate 廃止）
-- ================================================================

record G2toSO7Struct : Type₁ where
  field
    ℚ   : Type
    0ℚ  : ℚ
    _+q_ : ℚ → ℚ → ℚ
    -q_  : ℚ → ℚ

    A    : Type
    0A   : A
    unit : A
    mul  : A → A → A
    scalar : A → ℚ
    dot  : A → A → ℚ

    D-map : A → A → A → A
    D-unit-proof : ∀ a b → D-map a b unit ≡ 0A
    D-map-antisym : ∀ a b x y →
      (dot (D-map a b x) y) +q (dot x (D-map a b y)) ≡ 0ℚ

  ImA-type : Type
  ImA-type = Σ[ x ∈ A ] (scalar x ≡ 0ℚ)

  π : ImA-type → A
  π = fst

  field
    D-preserves-im : ∀ a b (u : ImA-type) →
      scalar (D-map a b (π u)) ≡ 0ℚ

-- ================================================================
-- 2. so(7) と g₂ の定義（モジュールパラメータ化）
-- ================================================================

module _ (𝒮 : G2toSO7Struct) where
  open G2toSO7Struct 𝒮

  record so7-Element : Type where
    field
      F : ImA-type → ImA-type
      antisym : ∀ u v →
        (dot (π (F u)) (π v)) +q (dot (π u) (π (F v))) ≡ 0ℚ

  record g2-Element : Type where
    field
      a b : ImA-type

    act : A → A
    act = D-map (π a) (π b)

  g2→so7 : g2-Element → so7-Element
  g2→so7 g = record
    { F = λ u → (g2-Element.act g (π u)) , D-preserves-im (π (g2-Element.a g)) (π (g2-Element.b g)) u
    ; antisym = λ u v → D-map-antisym (π (g2-Element.a g)) (π (g2-Element.b g)) (π u) (π v)
    }

-- ================================================================
-- 3. 今後の展望：Lie Bracket の一致
-- ================================================================
-- ここで g2 側のブラケットと so7 側のブラケットが、
-- この g2→so7 射を介して保存されることを証明していく道筋ができました。
