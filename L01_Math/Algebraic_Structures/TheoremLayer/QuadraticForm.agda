{-# OPTIONS --cubical --guardedness #-}

-- ================================================================
-- Quadratic Forms over ℚ on Abelian Groups
-- ================================================================

module UMIN.L01_Math.Algebraic_Structures.TheoremLayer.QuadraticForm where

open import Cubical.Foundations.Prelude

-- ================================================================
-- ℚ (rational field)
-- ================================================================

postulate
  ℚ : Type
  isSetℚ : isSet ℚ
  0ℚ 1ℚ 2ℚ : ℚ
  _+q_ _-q_ _*q_ _/q_ : ℚ → ℚ → ℚ
  -q_ : ℚ → ℚ

  +q-comm   : ∀ a b → a +q b ≡ b +q a
  +q-assoc  : ∀ a b c → (a +q b) +q c ≡ a +q (b +q c)
  +q-0      : ∀ a → a +q 0ℚ ≡ a
  +q-inv    : ∀ a → a +q (-q a) ≡ 0ℚ
  +q-cancel : ∀ {a b c} → a +q c ≡ b +q c → a ≡ b
  *q-comm   : ∀ a b → a *q b ≡ b *q a
  *q-1      : ∀ a → a *q 1ℚ ≡ a
  *q-dist-l : ∀ a b c → a *q (b +q c) ≡ (a *q b) +q (a *q c)
  /q-half   : ∀ a b → (a +q b) /q 2ℚ ≡ (a /q 2ℚ) +q (b /q 2ℚ)
  /q-0      : 0ℚ /q 2ℚ ≡ 0ℚ
  2*-/2     : ∀ a → (2ℚ *q a) /q 2ℚ ≡ a
  -q-sub    : ∀ a b → a -q b ≡ a +q (-q b)
  -q-self   : ∀ a → a -q a ≡ 0ℚ

infixl 6 _+q_ _-q_
infixl 7 _*q_ _/q_

-- ================================================================
-- Abelian Group
-- ================================================================

record AbelianGroup (G : Type) : Type where
  field
    ε     : G
    _⊕_   : G → G → G
    ⊖_    : G → G
    ⊕-assoc : ∀ x y z → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
    ⊕-comm  : ∀ x y → x ⊕ y ≡ y ⊕ x
    ⊕-unit  : ∀ x → x ⊕ ε ≡ x
    ⊕-inv   : ∀ x → x ⊕ (⊖ x) ≡ ε
  _⊖_ : G → G → G
  x ⊖ y = x ⊕ (⊖ y)

-- ================================================================
-- Quadratic Form record
-- ================================================================

record QuadraticForm (G : Type) (grp : AbelianGroup G) : Type₁ where
  open AbelianGroup grp

  field
    scale : ℚ → G → G
    q : G → ℚ
    q-0   : q ε ≡ 0ℚ
    q-neg : ∀ x → q (⊖ x) ≡ q x
    q-PL  : ∀ x y → (q (x ⊕ y)) +q (q (x ⊖ y)) ≡ 2ℚ *q ((q x) +q (q y))
    q-SC  : ∀ r x → q (scale r x) ≡ (r *q r) *q (q x)
    scale-dist : ∀ r x y → scale r (x ⊕ y) ≡ (scale r x) ⊕ (scale r y)

  -- 数式を整理しました
  B : G → G → ℚ
  B x y = (((q (x ⊕ y)) -q (q x)) -q (q y)) /q 2ℚ

  postulate
    identity-† : ∀ x y z →
      (q ((x ⊕ y) ⊕ z)) +q (q x) +q (q y) +q (q z)
      ≡ (q (x ⊕ y)) +q (q (x ⊕ z)) +q (q (y ⊕ z))

    B-add-l : ∀ x y z → B (x ⊕ y) z ≡ (B x z) +q (B y z)

  postulate
    lemma-comm-sub : ∀ a b c → ((a -q b) -q c) /q 2ℚ ≡ ((a -q c) -q b) /q 2ℚ

  B-sym : ∀ x y → B x y ≡ B y x
  B-sym x y = cong (λ n → (((n -q q x) -q q y) /q 2ℚ)) (cong q (⊕-comm x y))
            ∙ lemma-comm-sub (q (y ⊕ x)) (q x) (q y)

  B-add-r : ∀ x y z → B x (y ⊕ z) ≡ (B x y) +q (B x z)
  B-add-r x y z =
    B-sym x (y ⊕ z)
    ∙ B-add-l y z x
    ∙ cong₂ _+q_ (B-sym y x) (B-sym z x)

  postulate
    B-neg-l : ∀ x y → B (⊖ x) y ≡ -q (B x y)

  B-neg-r : ∀ x y → B x (⊖ y) ≡ -q (B x y)
  B-neg-r x y = B-sym x (⊖ y) ∙ B-neg-l y x ∙ cong -q_ (B-sym y x)

  postulate
    B-zero-r : ∀ x → B x ε ≡ 0ℚ

  B-zero-l : ∀ x → B ε x ≡ 0ℚ
  B-zero-l x = B-sym ε x ∙ B-zero-r x

  postulate
    B-scale-l : ∀ r x y → B (scale r x) y ≡ r *q (B x y)

  B-scale-r : ∀ r x y → B x (scale r y) ≡ r *q (B x y)
  B-scale-r r x y = B-sym x (scale r y) ∙ B-scale-l r y x ∙ cong (r *q_) (B-sym y x)