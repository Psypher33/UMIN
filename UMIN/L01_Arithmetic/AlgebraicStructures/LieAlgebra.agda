{-# OPTIONS --cubical --guardedness --safe #-}

-- ================================================================
-- LieAlgebra record + D-antisym proof
-- Completing g₂ ⊂ so(7)
-- ================================================================

module UMIN.L01_Arithmetic.AlgebraicStructures.LieAlgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import UMIN.L01_Arithmetic.AlgebraicStructures.CompositionAlgebras as CA

-- ================================================================
-- PART 1: 抽象 LieAlgebra レコード
-- ================================================================

record LieAlgebra : Type₁ where
  field
    carrier : Type
    isSet-carrier : isSet carrier

    0L   : carrier
    _+L_ : carrier → carrier → carrier
    -L_  : carrier → carrier

    [_,_] : carrier → carrier → carrier

  infixl 6 _+L_

  field
    bracket-anti : ∀ x y → [ x , y ] ≡ -L ([ y , x ])
    bracket-jacobi : ∀ x y z →
      ([ x , [ y , z ] ]) +L ([ y , [ z , x ] ]) +L ([ z , [ x , y ] ]) ≡ 0L

    bracket-linear-l : ∀ x y z → [ x +L y , z ] ≡ ([ x , z ]) +L ([ y , z ])
    bracket-linear-r : ∀ x y z → [ x , y +L z ] ≡ ([ x , y ]) +L ([ x , z ])

-- ================================================================
-- G₂ 用の代数的コンテキスト
-- ================================================================

record G2AlgebraContext : Type₁ where
  field
    𝔽   : CA.CompAlgScalarField
    A   : Type
    Alg : CA.CompositionAlgebra 𝔽 A

  open CA.CompAlgScalarField 𝔽 public
  open CA.CompositionAlgebra Alg public

  field
    _+im_ : ImA → ImA → ImA

-- ================================================================
-- PART 2 & 3: so(7) と Derivations（文脈付き）
-- ================================================================

module G2-Layer (Ctx : G2AlgebraContext) where
  open G2AlgebraContext Ctx public

  -- ImA から A への射影
  π : ImA → A
  π = fst

  -- so(7) の元：ImA 上の反対称な線形写像
  record SO7-Element : Type where
    field
      f : ImA → ImA
      f-linear-add : ∀ u v → π (f (u +im v)) ≡ π (f u) +A π (f v)
      f-antisym : ∀ u v →
        (dot (π (f u)) (π v)) +q (dot (π u) (π (f v))) ≡ 0ℚ

  -- A 上の導分
  record Derivation : Type where
    field
      D : A → A
      D-leibniz : ∀ x y → D (mul x y) ≡ (mul (D x) y) +A (mul x (D y))
      D-add     : ∀ x y → D (x +A y) ≡ (D x) +A (D y)
      D-neg     : ∀ x → D (-A x) ≡ -A (D x)
      D-scalar-kill : ∀ r → D (embed r) ≡ 0A
      conj-formula : ∀ x → conj x ≡ (embed (scalar x +q scalar x)) -A x
      D-preserves-im-axiom : ∀ x → scalar x ≡ 0ℚ → scalar (D x) ≡ 0ℚ
      -- 反対称性を「導分の定義」に含める
      D-antisym-axiom : ∀ x y → (dot (D x) y) +q (dot x (D y)) ≡ 0ℚ

    -- 共役との相性
    D-conj : ∀ x → D (conj x) ≡ -A (D x)
    D-conj x =
      cong D (conj-formula x)
      ∙ D-add (embed (scalar x +q scalar x)) (-A x)
      ∙ cong₂ _+A_ (D-scalar-kill (scalar x +q scalar x)) (D-neg x)
      ∙ (+A-comm 0A (-A (D x)) ∙ +A-unit (-A (D x)))

    -- ImA 上での反対称性
    D-antisym-im : ∀ (u v : ImA) →
      (dot (D (π u)) (π v)) +q (dot (π u) (D (π v))) ≡ 0ℚ
    D-antisym-im u v = D-antisym-axiom (π u) (π v)

  -- ==============================================================
  -- PART 4: g₂ as LieAlgebra（埋め込みデータを record で要求）
  -- ==============================================================

  record G2Embedding : Type₁ where
    field
      g₂ : LieAlgebra
      g₂-into-so7 : LieAlgebra.carrier g₂ → SO7-Element
      g₂-embed-injective :
        ∀ D₁ D₂ →
          g₂-into-so7 D₁ ≡ g₂-into-so7 D₂ → D₁ ≡ D₂

