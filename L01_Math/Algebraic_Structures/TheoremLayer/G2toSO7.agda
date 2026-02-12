{-# OPTIONS --cubical --guardedness #-}

module UMIN.L01_Math.Algebraic_Structures.TheoremLayer.G2toSO7 where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

-- ================================================================
-- 1. 基本公理（Q と A の構造）
-- ================================================================
postulate
  ℚ : Type
  0ℚ : ℚ
  _+q_ : ℚ → ℚ → ℚ
  -q_ : ℚ → ℚ
  
  A : Type
  0A : A  -- 修正：postulateブロック内で正しく宣言
  unit : A
  mul : A → A → A
  scalar : A → ℚ
  dot : A → A → ℚ
  
  D-map : A → A → A → A
  D-unit-proof : ∀ a b → D-map a b unit ≡ 0A
  D-map-antisym : ∀ a b x y → (dot (D-map a b x) y) +q (dot x (D-map a b y)) ≡ 0ℚ

ImA : Type
ImA = Σ[ x ∈ A ] (scalar x ≡ 0ℚ)

π : ImA → A
π = fst

postulate
  D-preserves-im : ∀ a b (u : ImA) → scalar (D-map a b (π u)) ≡ 0ℚ

-- ================================================================
-- 2. so(7) の構造定義
-- ================================================================
record so7-Element : Type where
  field
    F : ImA → ImA
    antisym : ∀ u v → (dot (π (F u)) (π v)) +q (dot (π u) (π (F v))) ≡ 0ℚ

-- ================================================================
-- 3. g₂ 要素の定義
-- ================================================================
record g2-Element : Type where
  field
    a b : ImA

  -- D-map をこの要素の作用（act）として定義
  act : A → A
  act = D-map (π a) (π b)

-- ================================================================
-- 4. g₂ ↪ so(7) 包含写像の実装
-- ================================================================
g2→so7 : g2-Element → so7-Element
g2→so7 g = record
  { F       = λ u → (g2-Element.act g (π u)) , D-preserves-im (π (g2-Element.a g)) (π (g2-Element.b g)) u
  ; antisym = λ u v → D-map-antisym (π (g2-Element.a g)) (π (g2-Element.b g)) (π u) (π v)
  }

-- ================================================================
-- 5. 今後の展望：Lie Bracket の一致
-- ================================================================
-- ここで g2 側のブラケットと so7 側のブラケットが、
-- この g2→so7 射を介して保存されることを証明していく道筋ができました。