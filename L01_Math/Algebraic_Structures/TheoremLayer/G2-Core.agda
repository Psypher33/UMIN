{-# OPTIONS --cubical --guardedness #-}

module UMIN.L01_Math.Algebraic_Structures.TheoremLayer.G2-Core where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

-- ================================================================
-- Algebra postulates
-- ================================================================

postulate
  ℚ : Type
  0ℚ 1ℚ : ℚ
  _+q_ _*q_ : ℚ → ℚ → ℚ
  -q_ : ℚ → ℚ
  +q-inv : ∀ a → a +q (-q a) ≡ 0ℚ
  +q-0   : ∀ a → a +q 0ℚ ≡ a

infixl 6 _+q_
infixl 7 _*q_

postulate
  A : Type
  0A : A
  _+A_ : A → A → A
  -A_ : A → A

infixl 6 _+A_

postulate
  +A-assoc : ∀ x y z → (x +A y) +A z ≡ x +A (y +A z)
  +A-comm  : ∀ x y → x +A y ≡ y +A x
  +A-unit  : ∀ x → x +A 0A ≡ x
  +A-inv   : ∀ x → x +A (-A x) ≡ 0A
  +A-idem  : ∀ x → x +A x ≡ x → x ≡ 0A

  unit : A
  mul : A → A → A
  embed : ℚ → A
  
  mul-unit-l : ∀ x → mul unit x ≡ x
  mul-unit-r : ∀ x → mul x unit ≡ x
  mul-dist-l : ∀ x y z → mul x (y +A z) ≡ (mul x y) +A (mul x z)
  mul-dist-r : ∀ x y z → mul (x +A y) z ≡ (mul x z) +A (mul y z)
  mul-0-l    : ∀ x → mul 0A x ≡ 0A
  mul-0-r    : ∀ x → mul x 0A ≡ 0A
  left-alt   : ∀ x y → mul x (mul x y) ≡ mul (mul x x) y
  right-alt  : ∀ x y → mul (mul y x) x ≡ mul y (mul x x)

  dot : A → A → ℚ
  dot-add-l : ∀ x y z → dot (x +A y) z ≡ (dot x z) +q (dot y z)
  dot-sym   : ∀ x y → dot x y ≡ dot y x
  dot-neg-l : ∀ x y → dot (-A x) y ≡ -q (dot x y)

  scalar : A → ℚ
  im : A → A
  im-scalar-zero : ∀ x → scalar (im x) ≡ 0ℚ

-- 追加（D-preserves-im 用）
postulate
  scalar-def : ∀ x → scalar x ≡ dot x unit
  dot-0-r    : ∀ x → dot x 0A ≡ 0ℚ

_-A_ : A → A → A
x -A y = x +A (-A y)

infixl 6 _-A_

ImA : Type
ImA = Σ[ x ∈ A ] (scalar x ≡ 0ℚ)

π : ImA → A
π = fst

postulate
  cross : ImA → ImA → ImA

-- ================================================================
-- PART 1: Derivation
-- ================================================================

record Derivation : Type where
  field
    D : A → A
    D-leibniz : ∀ x y → D (mul x y) ≡ (mul (D x) y) +A (mul x (D y))
    D-add     : ∀ x y → D (x +A y) ≡ (D x) +A (D y)
    D-neg     : ∀ x → D (-A x) ≡ -A (D x)
    D-scalar  : ∀ r → D (embed r) ≡ 0A
    D-antisym : ∀ x y → (dot (D x) y) +q (dot x (D y)) ≡ 0ℚ

  -- ============================
  -- Derived lemmas
  -- ============================

  D-unit-lemma : D unit ≡ (D unit) +A (D unit)
  D-unit-lemma =
      cong D (sym (mul-unit-l unit))
    ∙ D-leibniz unit unit
    ∙ cong₂ _+A_ (mul-unit-r (D unit)) (mul-unit-l (D unit))

  D-unit : D unit ≡ 0A
  D-unit = +A-idem (D unit) (sym D-unit-lemma)

  -- 一旦 postulate にして安定させる
  postulate
    D-preserves-im : ∀ (u : ImA) → scalar (D (π u)) ≡ 0ℚ

  D-im : ImA → ImA
  D-im u = D (π u) , D-preserves-im u

-- ================================================================
-- PART 2: Cross product preservation
-- ================================================================

module CrossPreservation (Der : Derivation) where
  open Derivation Der

  postulate
    ImA-add : ImA → ImA → ImA

  postulate
    D-cross-typed :
      ∀ (u v : ImA) →
        D-im (cross u v) ≡
        ImA-add (cross (D-im u) v)
                 (cross u (D-im v))

-- ================================================================
-- PART 3: Schafer Operators
-- ================================================================

L R : A → A → A
L a x = mul a x
R a x = mul x a

_-op_ : (A → A) → (A → A) → (A → A)
(F -op G) x = (F (G x)) -A (G (F x))

infixl 7 _-op_

D-gen-map : A → A → A → A
D-gen-map a b x =
  ((L a -op L b) x) +A
  ((L a -op R b) x) +A
  ((R a -op R b) x)

-- ================================================================
-- PART 4: Magic Square E8
-- ================================================================

postulate
  bracket-der : Derivation → Derivation → Derivation

record MagicSquareE8 : Type₁ where
  field
    Jordan-J : Type
    jordan-prod : Jordan-J → Jordan-J → Jordan-J
    trace-J : Jordan-J → ℚ
    Jordan-J₀ : Type
    f₄ : Type    
    e₈ : Type
    bracket-e₈ : e₈ → e₈ → e₈
    embed-g₂ : Derivation → e₈
    
    embed-compat :
      ∀ D₁ D₂ →
        bracket-e₈ (embed-g₂ D₁)
                   (embed-g₂ D₂)
        ≡ embed-g₂ (bracket-der D₁ D₂)