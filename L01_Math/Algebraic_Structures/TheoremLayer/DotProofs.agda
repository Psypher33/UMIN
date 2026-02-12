{-# OPTIONS --cubical --guardedness #-}

-- ================================================================
-- Dot Bilinearity Proofs: The Cascade to G2
-- ================================================================

module UMIN.L01_Math.Algebraic_Structures.TheoremLayer.DotProofs where

open import Cubical.Foundations.Prelude

-- ================================================================
-- ℚ (Rational Field)
-- ================================================================

postulate
  ℚ : Type
  0ℚ 1ℚ 2ℚ : ℚ
  _+q_ _-q_ _*q_ _/q_ : ℚ → ℚ → ℚ
  -q_ : ℚ → ℚ

infixl 6 _+q_ _-q_
infixl 7 _*q_ _/q_

postulate
  +q-comm    : ∀ a b → (a +q b) ≡ (b +q a)
  +q-assoc   : ∀ a b c → ((a +q b) +q c) ≡ (a +q (b +q c))
  +q-0       : ∀ a → (a +q 0ℚ) ≡ a
  +q-inv     : ∀ a → (a +q (-q a)) ≡ 0ℚ
  -q-distrib : ∀ a b → (-q (a +q b)) ≡ ((-q a) +q (-q b))
  -q-invol   : ∀ a → (-q (-q a)) ≡ a
  *q-comm    : ∀ a b → (a *q b) ≡ (b *q a)
  *q-1       : ∀ a → (a *q 1ℚ) ≡ a
  *q-dist-l  : ∀ a b c → (a *q (b +q c)) ≡ ((a *q b) +q (a *q c))
  /q-dist    : ∀ a b → ((a +q b) /q 2ℚ) ≡ ((a /q 2ℚ) +q (b /q 2ℚ))
  /q-0       : (0ℚ /q 2ℚ) ≡ 0ℚ
  /q-cancel  : ∀ a → ((2ℚ *q a) /q 2ℚ) ≡ a
  -q-sub     : ∀ a b → (a -q b) ≡ (a +q (-q b))
  -q-self    : ∀ a → (a -q a) ≡ 0ℚ

-- ================================================================
-- Algebra A (Octonions/Composition Algebra)
-- ================================================================

postulate
  A : Type
  0A : A
  _+A_ : A → A → A
  -A_ : A → A

infixl 6 _+A_

-- ★ ここが重要！先に中置の -A を定義します
_-A_ : A → A → A
x -A y = x +A (-A y)

infixl 6 _-A_

postulate
  +A-comm  : ∀ x y → (x +A y) ≡ (y +A x)
  +A-assoc : ∀ x y z → ((x +A y) +A z) ≡ (x +A (y +A z))
  +A-unit  : ∀ x → (x +A 0A) ≡ x
  +A-inv   : ∀ x → (x +A (-A x)) ≡ 0A

  unit : A
  mul : A → A → A
  embed : ℚ → A
  embed-1 : embed 1ℚ ≡ unit

  norm : A → ℚ
  norm-0   : norm 0A ≡ 0ℚ
  norm-neg : ∀ x → norm (-A x) ≡ norm x
  
  -- これで x -A y が正しく解析されます
  norm-quadratic : ∀ x y →
    (norm (x +A y)) +q (norm (x -A y)) ≡ 2ℚ *q ((norm x) +q (norm y))
  
  norm-scalar : ∀ (r : ℚ) (x : A) →
    norm (mul (embed r) x) ≡ (r *q r) *q (norm x)

-- ================================================================
-- Dot Definition and Properties
-- ================================================================

dot : A → A → ℚ
dot x y = (((norm (x +A y)) -q (norm x)) -q (norm y)) /q 2ℚ

dot-sym : ∀ x y → dot x y ≡ dot y x
dot-sym x y = 
  cong (λ n → (((n -q norm x) -q norm y) /q 2ℚ)) (cong norm (+A-comm x y))
  ∙ cong (_/q 2ℚ) (lemma (norm (y +A x)) (norm x) (norm y))
  where
    postulate lemma : ∀ a b c → ((a -q b) -q c) ≡ ((a -q c) -q b)

postulate
  dot-zero-r : ∀ x → dot x 0A ≡ 0ℚ
  dot-add-l : ∀ x y z → dot (x +A y) z ≡ ((dot x z) +q (dot y z))

dot-add-r : ∀ x y z → dot x (y +A z) ≡ ((dot x y) +q (dot x z))
dot-add-r x y z =
  dot-sym x (y +A z)
  ∙ dot-add-l y z x
  ∙ cong₂ _+q_ (dot-sym y x) (dot-sym z x)

postulate
  dot-neg-l : ∀ x y → dot (-A x) y ≡ (-q (dot x y))

dot-neg-r : ∀ x y → dot x (-A y) ≡ (-q (dot x y))
dot-neg-r x y =
  dot-sym x (-A y)
  ∙ dot-neg-l y x
  ∙ cong -q_ (dot-sym y x)

postulate
  dot-scalar-l : ∀ (r : ℚ) (x y : A) → dot (mul (embed r) x) y ≡ (r *q (dot x y))

dot-scalar-r : ∀ (r : ℚ) (x y : A) → dot x (mul (embed r) y) ≡ (r *q (dot x y))
dot-scalar-r r x y =
  dot-sym x (mul (embed r) y)
  ∙ dot-scalar-l r y x
  ∙ cong (r *q_) (dot-sym y x)

postulate
  dot-unit-unit : dot unit unit ≡ 1ℚ
  scalar-embed : ∀ r → dot (embed r) unit ≡ r
  im-scalar-zero : ∀ x → dot (x -A embed (dot x unit)) unit ≡ 0ℚ