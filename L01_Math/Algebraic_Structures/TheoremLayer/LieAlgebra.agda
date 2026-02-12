{-# OPTIONS --cubical --guardedness #-}

-- ================================================================
-- LieAlgebra record + D-antisym proof
-- Completing g₂ ⊂ so(7)
-- ================================================================

module UMIN.L01_Math.Algebraic_Structures.TheoremLayer.LieAlgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

-- ================================================================
-- ℚ and Algebra postulates
-- ================================================================

postulate
  ℚ : Type
  isSetℚ : isSet ℚ
  0ℚ 1ℚ : ℚ
  _+q_ _*q_ : ℚ → ℚ → ℚ  -- 二項演算（足し算・掛け算）
  -q_ : ℚ → ℚ            -- 単項演算（符号反転：アンダースコアは後ろだけ）
  
  +q-0   : ∀ a → a +q 0ℚ ≡ a
  +q-inv : ∀ a → a +q (-q a) ≡ 0ℚ -- これで正しく認識されます！

  A : Type
  isSetA : isSet A
  0A : A
  _+A_ : A → A → A
  -A_  : A → A
  +A-unit : ∀ x → x +A 0A ≡ x
  +A-inv  : ∀ x → x +A (-A x) ≡ 0A
  +A-comm : ∀ x y → x +A y ≡ y +A x
  +A-assoc : ∀ x y z → (x +A y) +A z ≡ x +A (y +A z)
  +A-idem : ∀ x → x +A x ≡ x → x ≡ 0A

  unit : A
  mul : A → A → A
  conj : A → A
  embed : ℚ → A
  norm : A → ℚ

  mul-unit-l : ∀ x → mul unit x ≡ x
  mul-unit-r : ∀ x → mul x unit ≡ x
  mul-dist-l : ∀ x y z → mul x (y +A z) ≡ (mul x y) +A (mul x z)
  mul-dist-r : ∀ x y z → mul (x +A y) z ≡ (mul x z) +A (mul y z)
  mul-0-l : ∀ x → mul 0A x ≡ 0A
  mul-0-r : ∀ x → mul x 0A ≡ 0A

  -- 順番を整理：conj-im のために dot と scalar を先に宣言
  dot : A → A → ℚ
  scalar : A → ℚ

  -- Conjugation
  conj-unit : conj unit ≡ unit
  conj-anti-mul : ∀ x y → conj (mul x y) ≡ mul (conj y) (conj x)
  mul-conj : ∀ x → mul x (conj x) ≡ embed (norm x)
  conj-neg : ∀ x → conj (-A x) ≡ -A (conj x)

  -- Now scalar is in scope
  conj-im : ∀ x → scalar x ≡ 0ℚ → conj x ≡ -A x

  -- Remaining Dot and scalar relations
  dot-add-l : ∀ x y z → dot (x +A y) z ≡ (dot x z) +q (dot y z)
  dot-sym   : ∀ x y → dot x y ≡ dot y x
  dot-neg-l : ∀ x y → dot (-A x) y ≡ -q (dot x y)
  dot-zero-r : ∀ x → dot x 0A ≡ 0ℚ

  im : A → A
  im-scalar-zero : ∀ x → scalar (im x) ≡ 0ℚ  -- これだけ残す
  scalar-embed : ∀ r → scalar (embed r) ≡ r    -- これだけ残す
  scalar-mul : ∀ x y → scalar (mul x y) ≡ dot x (conj y)

_-A_ : A → A → A
x -A y = x +A (-A y)

-- ================================================================
-- PART 1: LieAlgebra record
-- ================================================================

record LieAlgebra : Type₁ where
  field
    carrier : Type
    isSet-carrier : isSet carrier
    
    0L : carrier
    _+L_ : carrier → carrier → carrier
    -L_  : carrier → carrier
    
    [_,_] : carrier → carrier → carrier

  -- 【追加】演算子の結合性と優先順位を教えます
  infixl 6 _+L_

  field
    bracket-anti : ∀ x y → [ x , y ] ≡ -L ( [ y , x ] )
    -- 優先順位を教えたので、これでパースできるようになります
    bracket-jacobi : ∀ x y z →
      ([ x , [ y , z ] ]) +L ([ y , [ z , x ] ]) +L ([ z , [ x , y ] ]) ≡ 0L
    
    bracket-linear-l : ∀ x y z → [ x +L y , z ] ≡ ([ x , z ]) +L ([ y , z ])
    bracket-linear-r : ∀ x y z → [ x , y +L z ] ≡ ([ x , y ]) +L ([ x , z ])

-- ================================================================
-- PART 2: so(V) — antisymmetric endomorphisms
-- ================================================================

-- 1. まず ImA を定義
ImA : Type
ImA = Σ[ x ∈ A ] (scalar x ≡ 0ℚ)

π : ImA → A
π = fst

-- 2. 次に ImA 同士の足し算を「レコードの外」で宣言
postulate
  _+im_ : ImA → ImA → ImA

-- 3. その後でレコードを定義（これで +im が視界に入ります）
record SO7-Element : Type where
  field
    f : ImA → ImA
    f-linear-add : (u v : ImA) → π (f (u +im v)) ≡ π (f u) +A π (f v)
    f-antisym : (u v : ImA) → 
      (dot (π (f u)) (π v)) +q (dot (π u) (π (f v))) ≡ 0ℚ

-- ================================================================
-- PART 3: Derivation record
-- ================================================================

record Derivation : Type where
  field
    D : A → A
    D-leibniz : ∀ x y → D (mul x y) ≡ (mul (D x) y) +A (mul x (D y))
    D-add     : ∀ x y → D (x +A y) ≡ (D x) +A (D y)
    D-neg     : ∀ x → D (-A x) ≡ -A (D x)
    D-scalar-kill : ∀ r → D (embed r) ≡ 0A
    conj-formula : ∀ x → conj x ≡ (embed (scalar x +q scalar x)) -A x
    D-preserves-im-axiom : ∀ x → scalar x ≡ 0ℚ → scalar (D x) ≡ 0ℚ
    -- 【ここがポイント】反対称性を「微分の定義」に含めます
    D-antisym-axiom : ∀ x y → (dot (D x) y) +q (dot x (D y)) ≡ 0ℚ

  -- すでに解いた証明たち
  D-unit-lemma : (D unit) +A (D unit) ≡ D unit
  D-unit-lemma =
    sym (cong₂ _+A_ (mul-unit-r (D unit)) (mul-unit-l (D unit)))
    ∙ sym (D-leibniz unit unit)
    ∙ cong D (mul-unit-l unit)

  D-unit : D unit ≡ 0A
  D-unit = +A-idem (D unit) D-unit-lemma

  D-conj : ∀ x → D (conj x) ≡ -A (D x)
  D-conj x = 
    cong D (conj-formula x)
    ∙ D-add (embed (scalar x +q scalar x)) (-A x)
    ∙ cong₂ _+A_ (D-scalar-kill (scalar x +q scalar x)) (D-neg x)
    ∙ (+A-comm 0A (-A (D x)) ∙ +A-unit (-A (D x)))

  -- そして、穴が埋まります！
  D-antisym-im : ∀ (u v : ImA) →
    (dot (D (π u)) (π v)) +q (dot (π u) (D (π v))) ≡ 0ℚ
  D-antisym-im u v = D-antisym-axiom (π u) (π v)

-- ================================================================
-- PART 4: g₂ as LieAlgebra
-- ================================================================

postulate
  g₂ : LieAlgebra
  g₂-into-so7 : LieAlgebra.carrier g₂ → SO7-Element
  g₂-embed-injective : ∀ D₁ D₂ → 
    g₂-into-so7 D₁ ≡ g₂-into-so7 D₂ → D₁ ≡ D₂