{-# OPTIONS --cubical --guardedness --safe #-}

-- ================================================================
-- Composition Algebra — Definitive Version (v4) — Safe
-- ================================================================

module UMIN.L01_Math.Algebraic_Structures.TheoremLayer.CompositionAlgebras-v4 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma

-- ================================================================
-- Part 1: スカラー体（ℚ）を record で受け取る（postulate 廃止）
-- ================================================================

record CompAlgScalarField : Type₁ where
  field
    ℚ     : Type
    isSetℚ : isSet ℚ
    0ℚ 1ℚ 2ℚ 4ℚ : ℚ
    _+q_ _*q_ _-q_ _/q_ : ℚ → ℚ → ℚ
    -q_   : ℚ → ℚ

    +q-comm    : ∀ a b → (a +q b) ≡ (b +q a)
    +q-assoc   : ∀ a b c → ((a +q b) +q c) ≡ (a +q (b +q c))
    +q-0       : ∀ a → (a +q 0ℚ) ≡ a
    +q-inv     : ∀ a → (a +q (-q a)) ≡ 0ℚ
    *q-comm    : ∀ a b → (a *q b) ≡ (b *q a)
    *q-assoc   : ∀ a b c → ((a *q b) *q c) ≡ (a *q (b *q c))
    *q-1       : ∀ a → (a *q 1ℚ) ≡ a
    *q-0       : ∀ a → (a *q 0ℚ) ≡ 0ℚ
    *q-dist-l  : ∀ a b c → (a *q (b +q c)) ≡ ((a *q b) +q (a *q c))
    /q-cancel  : ∀ a → ((a +q a) /q 2ℚ) ≡ a
    /q-dist    : ∀ a b → ((a +q b) /q 2ℚ) ≡ ((a /q 2ℚ) +q (b /q 2ℚ))
    /q-0       : (0ℚ /q 2ℚ) ≡ 0ℚ
    -q-cancel  : ∀ a → (a -q a) ≡ 0ℚ
    -q-sub     : ∀ a b → (a -q b) ≡ (a +q (-q b))
    2ℚ-def     : 2ℚ ≡ (1ℚ +q 1ℚ)

  infixl 6 _+q_ _-q_
  infixl 7 _*q_ _/q_

-- ================================================================
-- Part 2: AdditiveGroup
-- ================================================================

record AdditiveGroup (A : Type) : Type where
  field
    0A    : A
    _+A_  : A → A → A
    -A_   : A → A
    +A-assoc : ∀ x y z → ((x +A y) +A z) ≡ (x +A (y +A z))
    +A-comm  : ∀ x y → (x +A y) ≡ (y +A x)
    +A-unit  : ∀ x → (x +A 0A) ≡ x
    +A-inv   : ∀ x → (x +A (-A x)) ≡ 0A
  _-A_ : A → A → A
  x -A y = x +A (-A y)

-- ================================================================
-- Part 3 & 4: CompositionAlgebra record（𝔽 を引数に、dot 補題はフィールド）
-- ================================================================

record CompositionAlgebra (𝔽 : CompAlgScalarField) (A : Type) : Type₁ where
  open CompAlgScalarField 𝔽

  field
    isSetA   : isSet A
    addGroup : AdditiveGroup A
  open AdditiveGroup addGroup public

  field
    unit : A
    mul  : A → A → A
    conj : A → A
    embed : ℚ → A
    embed-0       : embed 0ℚ ≡ 0A
    embed-1       : embed 1ℚ ≡ unit
    embed-hom-add : ∀ p q → embed (p +q q) ≡ (embed p) +A (embed q)
    embed-hom-mul : ∀ p q → embed (p *q q) ≡ mul (embed p) (embed q)
    embed-injective : ∀ p q → embed p ≡ embed q → p ≡ q
    mul-unit-l : ∀ x → mul unit x ≡ x
    mul-unit-r : ∀ x → mul x unit ≡ x
    conj-conj     : ∀ x   → conj (conj x) ≡ x
    conj-anti-mul : ∀ x y → conj (mul x y) ≡ mul (conj y) (conj x)
    conj-unit     : conj unit ≡ unit
    mul-dist-l : ∀ x y z → mul x (y +A z) ≡ (mul x y) +A (mul x z)
    mul-dist-r : ∀ x y z → mul (x +A y) z ≡ (mul x z) +A (mul y z)
    norm : A → ℚ
    norm-mul : ∀ x y → norm (mul x y) ≡ (norm x) *q (norm y)
    norm-unit : norm unit ≡ 1ℚ
    norm-0    : norm 0A ≡ 0ℚ
    norm-neg  : ∀ x → norm (-A x) ≡ norm x
    conj-norm : ∀ x → norm (conj x) ≡ norm x
    mul-conj : ∀ x → mul x (conj x) ≡ embed (norm x)
    norm-quadratic : ∀ x y →
      (norm (x +A y)) +q (norm (x -A y)) ≡
      (2ℚ *q ((norm x) +q (norm y)))
    norm-scalar : ∀ (r : ℚ) (x : A) →
      norm (mul (embed r) x) ≡ ((r *q r) *q (norm x))
    left-alt  : ∀ x y → mul x (mul x y) ≡ mul (mul x x) y
    right-alt : ∀ x y → mul (mul y x) x ≡ mul y (mul x x)

  dot : A → A → ℚ
  dot x y = (((norm (x +A y)) -q (norm x)) -q (norm y)) /q 2ℚ

  field
    dot-sym : ∀ x y → dot x y ≡ dot y x
    dot-zero-r : ∀ x → dot x 0A ≡ 0ℚ
    dot-add-l : ∀ x y z → dot (x +A y) z ≡ ((dot x z) +q (dot y z))
    dot-scalar-l : ∀ (r : ℚ) (x y : A) →
      dot (mul (embed r) x) y ≡ (r *q (dot x y))
    dot-neg-l : ∀ x y → dot (-A x) y ≡ (-q (dot x y))
    dot-unit-unit : dot unit unit ≡ 1ℚ
    scalar-embed : ∀ r → dot (embed r) unit ≡ r

  dot-zero-l : ∀ x → dot 0A x ≡ 0ℚ
  dot-zero-l x = dot-sym 0A x ∙ dot-zero-r x

  dot-add-r : ∀ x y z → dot x (y +A z) ≡ ((dot x y) +q (dot x z))
  dot-add-r x y z =
    dot-sym x (y +A z) ∙ dot-add-l y z x ∙ cong₂ _+q_ (dot-sym y x) (dot-sym z x)

  dot-scalar-r : ∀ (r : ℚ) (x y : A) →
    dot x (mul (embed r) y) ≡ (r *q (dot x y))
  dot-scalar-r r x y =
    dot-sym x (mul (embed r) y) ∙ dot-scalar-l r y x ∙ cong (r *q_) (dot-sym y x)

  scalar : A → ℚ
  scalar x = dot x unit

  im : A → A
  im x = x -A embed (scalar x)

  im-scalar-zero : ∀ x → scalar (im x) ≡ 0ℚ
  im-scalar-zero x =
    dot-add-l x (-A embed (scalar x)) unit
    ∙ cong (_+q (dot (-A embed (scalar x)) unit)) (refl {x = scalar x})
    ∙ cong (scalar x +q_) (dot-neg-l (embed (scalar x)) unit ∙ cong -q_ (scalar-embed (scalar x)))
    ∙ +q-inv (scalar x)

  cross-raw : A → A → A
  cross-raw u v = im (mul u v)

  ImA : Type
  ImA = Σ[ x ∈ A ] (scalar x ≡ 0ℚ)

  cross : ImA → ImA → ImA
  cross (u , pu) (v , pv) = (cross-raw u v) , im-scalar-zero (mul u v)

  φ : ImA → ImA → ImA → ℚ
  φ u v (w , pw) = dot (fst (cross u v)) w

-- ================================================================
-- Part 5, 6, 7: G₂ と CD は 𝔽 付きでパラメータ化
-- ================================================================

module G₂-Definition (𝔽 : CompAlgScalarField) (A : Type) (Alg : CompositionAlgebra 𝔽 A) where
  open CompAlgScalarField 𝔽
  open CompositionAlgebra Alg
  record G₂-Element : Type₁ where
    field
      f : ImA → ImA
      f-equiv : isEquiv f
      preserves-φ : ∀ u v w → φ (f u) (f v) (f w) ≡ φ u v w

module CD-Step (𝔽 : CompAlgScalarField) (A : Type) (Alg : CompositionAlgebra 𝔽 A) where
  open CompAlgScalarField 𝔽
  open CompositionAlgebra Alg
  CD : Type
  CD = A × A
  mul-CD : CD → CD → CD
  mul-CD (a , b) (c , d) = ((mul a c) -A (mul (conj d) b)) , ((mul d a) +A (mul b (conj c)))
  conj-CD : CD → CD
  conj-CD (a , b) = (conj a , -A b)
  norm-CD : CD → ℚ
  norm-CD (a , b) = ((norm a) +q (norm b))

-- ================================================================
-- 実例は postulate 廃止：塔を record で受け取る
-- ================================================================

record OctonionTower (𝔽 : CompAlgScalarField) : Type₁ where
  open CompAlgScalarField 𝔽
  field
    ℚ-alg : CompositionAlgebra 𝔽 ℚ
    ℂ : Type
    ℂ-alg : CompositionAlgebra 𝔽 ℂ
    ℍ : Type
    ℍ-alg : CompositionAlgebra 𝔽 ℍ
    𝕆 : Type
    𝕆-alg : CompositionAlgebra 𝔽 𝕆

-- 従来の Octonions 相当を使う場合は、OctonionTower の値を別ファイルで
-- 構成（または公理として渡す）して open してください。

module Octonions (𝔽 : CompAlgScalarField) (Tower : OctonionTower 𝔽) where
  open CompAlgScalarField 𝔽
  open OctonionTower Tower
  module ℚStep = CD-Step 𝔽 ℚ ℚ-alg
  -- ℚStep.CD と ℂ が一致するような Tower を渡す想定
  module ℂStep = CD-Step 𝔽 ℂ ℂ-alg
  module ℍStep = CD-Step 𝔽 ℍ ℍ-alg
  module 𝕆Step = CD-Step 𝔽 𝕆 𝕆-alg
