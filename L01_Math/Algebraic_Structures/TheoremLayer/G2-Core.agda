{-# OPTIONS --cubical --guardedness --safe #-}

module UMIN.L01_Math.Algebraic_Structures.TheoremLayer.G2-Core where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

-- ================================================================
-- §0. スカラー体（ℚ）の構造 — postulate 廃止、record で受け取り
-- ================================================================

record G2ScalarField : Type₁ where
  field
    ℚ     : Type
    0ℚ 1ℚ : ℚ
    _+q_ _*q_ : ℚ → ℚ → ℚ
    -q_   : ℚ → ℚ
    +q-inv : ∀ a → a +q (-q a) ≡ 0ℚ
    +q-0   : ∀ a → a +q 0ℚ ≡ a

  infixl 6 _+q_
  infixl 7 _*q_

-- ================================================================
-- §1. 代数 A の構造 — postulate 廃止、record で受け取り
-- ================================================================

record G2Algebra (𝔽 : G2ScalarField) : Type₁ where
  open G2ScalarField 𝔽

  field
    A     : Type
    0A    : A
    _+A_  : A → A → A
    -A_   : A → A
    +A-assoc : ∀ x y z → (x +A y) +A z ≡ x +A (y +A z)
    +A-comm  : ∀ x y → x +A y ≡ y +A x
    +A-unit  : ∀ x → x +A 0A ≡ x
    +A-inv   : ∀ x → x +A (-A x) ≡ 0A
    +A-idem  : ∀ x → x +A x ≡ x → x ≡ 0A

    unit  : A
    mul   : A → A → A
    embed : ℚ → A
    mul-unit-l : ∀ x → mul unit x ≡ x
    mul-unit-r : ∀ x → mul x unit ≡ x
    mul-dist-l : ∀ x y z → mul x (y +A z) ≡ (mul x y) +A (mul x z)
    mul-dist-r : ∀ x y z → mul (x +A y) z ≡ (mul x z) +A (mul y z)
    mul-0-l    : ∀ x → mul 0A x ≡ 0A
    mul-0-r    : ∀ x → mul x 0A ≡ 0A
    left-alt   : ∀ x y → mul x (mul x y) ≡ mul (mul x x) y
    right-alt  : ∀ x y → mul (mul y x) x ≡ mul y (mul x x)

    dot   : A → A → ℚ
    dot-add-l : ∀ x y z → dot (x +A y) z ≡ (dot x z) +q (dot y z)
    dot-sym   : ∀ x y → dot x y ≡ dot y x
    dot-neg-l : ∀ x y → dot (-A x) y ≡ -q (dot x y)
    dot-0-r   : ∀ x → dot x 0A ≡ 0ℚ

    scalar : A → ℚ
    scalar-def : ∀ x → scalar x ≡ dot x unit
    im     : A → A
    im-scalar-zero : ∀ x → scalar (im x) ≡ 0ℚ

  infixl 6 _+A_

  _-A_ : A → A → A
  x -A y = x +A (-A y)
  infixl 6 _-A_

  ImA-type : Type
  ImA-type = Σ[ x ∈ A ] (scalar x ≡ 0ℚ)

  π : ImA-type → A
  π = fst

  field
    cross : ImA-type → ImA-type → ImA-type
    ImA-add : ImA-type → ImA-type → ImA-type

-- ================================================================
-- PART 1: Derivation（D-preserves-im は record のフィールドで要求）
-- ================================================================

module _ (𝔽 : G2ScalarField) (𝒜 : G2Algebra 𝔽) where
  open G2ScalarField 𝔽
  open G2Algebra 𝒜

  record Derivation : Type where
    field
      D : A → A
      D-leibniz : ∀ x y → D (mul x y) ≡ (mul (D x) y) +A (mul x (D y))
      D-add     : ∀ x y → D (x +A y) ≡ (D x) +A (D y)
      D-neg     : ∀ x → D (-A x) ≡ -A (D x)
      D-scalar  : ∀ r → D (embed r) ≡ 0A
      D-antisym : ∀ x y → (dot (D x) y) +q (dot x (D y)) ≡ 0ℚ
      D-preserves-im : ∀ (u : ImA-type) → scalar (D (π u)) ≡ 0ℚ

    D-im : ImA-type → ImA-type
    D-im u = D (π u) , D-preserves-im u

    field
      D-cross-typed : ∀ (u v : ImA-type) →
        D-im (cross u v) ≡ ImA-add (cross (D-im u) v) (cross u (D-im v))

    D-unit-lemma : D unit ≡ (D unit) +A (D unit)
    D-unit-lemma =
        cong D (sym (mul-unit-l unit))
      ∙ D-leibniz unit unit
      ∙ cong₂ _+A_ (mul-unit-r (D unit)) (mul-unit-l (D unit))

    D-unit : D unit ≡ 0A
    D-unit = +A-idem (D unit) (sym D-unit-lemma)

-- ================================================================
-- PART 2: Cross product preservation（公理は Derivation に統合済み）
-- ================================================================

module CrossPreservation (𝔽 : G2ScalarField) (𝒜 : G2Algebra 𝔽) (Der : Derivation 𝔽 𝒜) where
  open G2ScalarField 𝔽
  open G2Algebra 𝒜
  open Derivation Der

  -- D-cross-typed は Derivation のフィールドなので postulate 不要
  D-cross-typed′ : ∀ (u v : ImA-type) →
    D-im (cross u v) ≡ ImA-add (cross (D-im u) v) (cross u (D-im v))
  D-cross-typed′ = D-cross-typed

-- ================================================================
-- PART 3: Schafer Operators
-- ================================================================

module _ (𝔽 : G2ScalarField) (𝒜 : G2Algebra 𝔽) where
  open G2ScalarField 𝔽
  open G2Algebra 𝒜

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
-- PART 4: Magic Square E8（bracket-der は record のフィールドで要求）
-- ================================================================

module _ (𝔽 : G2ScalarField) (𝒜 : G2Algebra 𝔽) where
  open G2ScalarField 𝔽
  open G2Algebra 𝒜

  record MagicSquareE8 : Type₁ where
    field
      Jordan-J : Type
      jordan-prod : Jordan-J → Jordan-J → Jordan-J
      trace-J : Jordan-J → ℚ
      Jordan-J₀ : Type
      f₄ : Type
      e₈ : Type
      bracket-e₈ : e₈ → e₈ → e₈
      bracket-der : Derivation 𝔽 𝒜 → Derivation 𝔽 𝒜 → Derivation 𝔽 𝒜
      embed-g₂ : Derivation 𝔽 𝒜 → e₈
      embed-compat :
        ∀ D₁ D₂ →
          bracket-e₈ (embed-g₂ D₁) (embed-g₂ D₂)
          ≡ embed-g₂ (bracket-der D₁ D₂)
