{-# OPTIONS --cubical --guardedness #-}

module UMIN.L01_Math.Algebraic_Structures.TheoremLayer.LieG2 where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)  -- ★ これを追加

-- ================================================================
-- Postulates (Basic structures)
-- ================================================================

postulate
  ℚ : Type
  isSetℚ : isSet ℚ
  0ℚ 1ℚ : ℚ
  _+q_ _*q_ _-q_ : ℚ → ℚ → ℚ
  -q_ : ℚ → ℚ
  +q-inv : ∀ a → a +q (-q a) ≡ 0ℚ

infixl 6 _+q_
infixl 7 _*q_

postulate
  A : Type
  isSetA : isSet A
  0A : A
  _+A_ : A → A → A
  -A_ : A → A
  unit : A
  mul : A → A → A
  conj : A → A
  embed : ℚ → A
  norm : A → ℚ
  dot : A → A → ℚ
  scalar : A → ℚ
  im : A → A

infixl 6 _+A_

postulate
  mul-unit-l : ∀ x → mul unit x ≡ x
  mul-unit-r : ∀ x → mul x unit ≡ x
  mul-dist-l : ∀ x y z → mul x (y +A z) ≡ (mul x y) +A (mul x z)
  mul-dist-r : ∀ x y z → mul (x +A y) z ≡ (mul x z) +A (mul y z)
  left-alt   : ∀ x y → mul x (mul x y) ≡ mul (mul x x) y
  right-alt  : ∀ x y → mul (mul y x) x ≡ mul y (mul x x)

  dot-add-l : ∀ x y z → dot (x +A y) z ≡ (dot x z) +q (dot y z)
  dot-sym   : ∀ x y → dot x y ≡ dot y x
  dot-neg-l : ∀ x y → dot (-A x) y ≡ -q (dot x y)

  im-scalar-zero : ∀ x → scalar (im x) ≡ 0ℚ
  scalar-embed : ∀ r → scalar (embed r) ≡ r

ImA : Type
ImA = Σ[ x ∈ A ] (scalar x ≡ 0ℚ)

π : ImA → A
π = fst

-- ================================================================
-- PART 1 & 2: Derivation
-- ================================================================

record Derivation : Type where
  field
    D : A → A
    D-leibniz : ∀ x y → D (mul x y) ≡ (mul (D x) y) +A (mul x (D y))
    D-linear-add : ∀ x y → D (x +A y) ≡ (D x) +A (D y)
    D-linear-neg : ∀ x → D (-A x) ≡ -A (D x)

postulate
  bracket : Derivation → Derivation → Derivation

module DerivationProperties (Der : Derivation) where
  open Derivation Der

  postulate
    D-unit : D unit ≡ 0A
    D-preserves-im : ∀ (u : ImA) → scalar (D (π u)) ≡ 0ℚ
    D-antisym :
      ∀ (u v : ImA) →
        (dot (D (π u)) (π v)) +q
        (dot (π u) (D (π v))) ≡ 0ℚ

  D-im : ImA → ImA
  D-im u = D (π u) , D-preserves-im u

-- ================================================================
-- PART 3 & 5: Schafer Operators
-- ================================================================

L R : A → A → A
L a x = mul a x
R a x = mul x a

op-bracket : (A → A) → (A → A) → (A → A)
op-bracket F G x = (F (G x)) +A (-A (G (F x)))

D-gen : A → A → A → A
D-gen a b x =
  (op-bracket (L a) (L b) x) +A
  (op-bracket (L a) (R b) x) +A
  (op-bracket (R a) (R b) x)

-- ================================================================
-- PART 6: Triality
-- ================================================================

record Triality : Type₁ where
  field
    V S⁺ S⁻ : Type
    t : V → S⁺ → S⁻ → ℚ

-- ================================================================
-- PART 7: E8 Bridge
-- ================================================================

postulate
  e₈ : Type
  ε-zero : e₈
  _+A'_ : e₈ → e₈ → e₈

infixl 6 _+A'_

record E8-LieAlgebra : Type₁ where
  field
    dim-e₈ : ℕ
    bracket-e₈ : e₈ → e₈ → e₈

    jacobi :
      ∀ x y z →
        bracket-e₈ x (bracket-e₈ y z) +A'
        (bracket-e₈ y (bracket-e₈ z x) +A'
        bracket-e₈ z (bracket-e₈ x y))
        ≡ ε-zero

    g₂-embedding : Derivation → e₈

    g₂-compat :
      ∀ D₁ D₂ →
        bracket-e₈ (g₂-embedding D₁) (g₂-embedding D₂)
        ≡ g₂-embedding (bracket D₁ D₂)