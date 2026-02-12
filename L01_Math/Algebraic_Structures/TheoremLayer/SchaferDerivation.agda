{-# OPTIONS --cubical --guardedness #-}

module UMIN.L01_Math.Algebraic_Structures.TheoremLayer.SchaferDerivation where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

-- ================================================================
-- Postulates
-- ================================================================
postulate
  ⊥ : Type
  ℚ : Type
  0ℚ : ℚ
  _+q_ : ℚ → ℚ → ℚ
  -q_ : ℚ → ℚ
  +q-inv : (a : ℚ) → a +q (-q a) ≡ 0ℚ
  +q-unit : (a : ℚ) → a +q 0ℚ ≡ a

  A : Type
  0A : A
  _+A_ : A → A → A
  -A_  : A → A
  +A-comm  : (x y : A) → x +A y ≡ y +A x
  +A-assoc : (x y z : A) → (x +A y) +A z ≡ x +A (y +A z)
  +A-unit  : (x : A) → x +A 0A ≡ x
  +A-inv   : (x : A) → x +A (-A x) ≡ 0A

  unit : A
  mul : A → A → A
  mul-unit-l : (x : A) → mul unit x ≡ x
  mul-unit-r : (x : A) → mul x unit ≡ x

  scalar : A → ℚ
  dot : A → A → ℚ
  
  -- 幾何学的な基本公理
  dot-unit : (x : A) → dot x unit ≡ scalar x
  dot-zero : (x : A) → dot x 0A ≡ 0ℚ

-- ================================================================
-- Definitions
-- ================================================================
infixl 6 _+A_
infixl 6 _-A_

_-A_ : A → A → A
x -A y = x +A (-A y)

ImA : Type
ImA = Σ[ x ∈ A ] (scalar x ≡ 0ℚ)

π : ImA → A
π = fst

D-map : A → A → A → A
D-map a b x = 
  ((mul a (mul b x)) -A (mul b (mul a x)))
  +A
  ((mul a (mul x b)) -A (mul (mul a x) b))
  +A
  ((mul (mul x b) a) -A (mul (mul x a) b))

postulate
  D-unit-proof : ∀ a b → D-map a b unit ≡ 0A
  D-map-antisym : ∀ a b x y → (dot (D-map a b x) y) +q (dot x (D-map a b y)) ≡ 0ℚ

-- ================================================================
-- THEOREM: D-map preserves Im
-- ================================================================
D-map-preserves-im : ∀ a b (u : ImA) → scalar (D-map a b (π u)) ≡ 0ℚ
D-map-preserves-im a b u = 
  let x = π u 
      D = D-map a b
  in
  -- 等式推論モジュールを使わず、パス結合演算子 ∙ で直接繋ぎます
  sym (dot-unit (D x)) 
  ∙ sym (+q-unit (dot (D x) unit))
  ∙ cong (λ k → (dot (D x) unit) +q k) (sym (dot-zero x))
  ∙ cong (λ k → (dot (D x) unit) +q (dot x k)) (sym (D-unit-proof a b))
  ∙ D-map-antisym a b x unit

-- ================================================================
-- 8. g₂ ⊂ so(7) の構築
-- ================================================================
record g2-Element : Type where
  field
    a b : ImA
  
  D : A → A
  D = D-map (π a) (π b)
  
  D-kills-unit : D unit ≡ 0A
  D-kills-unit = D-unit-proof (π a) (π b)
  
  D-preserves-im : ∀ (u : ImA) → scalar (D (π u)) ≡ 0ℚ
  D-preserves-im = D-map-preserves-im (π a) (π b)

  postulate
    D-is-leibniz : ∀ x y → D (mul x y) ≡ (mul (D x) y) +A (mul x (D y))