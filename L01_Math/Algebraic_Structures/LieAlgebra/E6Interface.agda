{-# OPTIONS --cubical --guardedness #-}

module UMIN.L01_Math.Algebraic_Structures.LieAlgebra.E6Interface where

open import Cubical.Foundations.Prelude
open import UMIN.L01_Math.Algebraic_Structures.LieAlgebra.FieldOfRationals
  using (𝕜; 𝕜-zero; 𝕜-one; _+𝕜_; _·𝕜_; -𝕜_; ratEmbed; posRat)
open import UMIN.L01_Math.Algebraic_Structures.LieAlgebra.AlbertAlgebra
  using (𝔍ᶜ; _∘_; tr-𝔍; _+𝔍_; -𝔍_; _⊛𝔍_; mk𝔍; 𝕆-zero)

-- ================================================================
-- §1. F4 Lie環 (Albert代数 𝔍ᶜ の自己導来環)
-- ================================================================
-- D(X ∘ Y) = (DX) ∘ Y + X ∘ (DY) を満たす線形写像 D : 𝔍ᶜ → 𝔍ᶜ
record F4-Lie : Type where
  constructor mkF4
  field
    deriv : 𝔍ᶜ → 𝔍ᶜ
    is-derivation : (X Y : 𝔍ᶜ) → deriv (X ∘ Y) ≡ (deriv X ∘ Y) +𝔍 (X ∘ deriv Y)

-- F4 の線形構造と Lie 積 [D₁, D₂] = D₁D₂ - D₂D₁
postulate
  F4-zero : F4-Lie
  _+F4_   : F4-Lie → F4-Lie → F4-Lie
  -F4     : F4-Lie → F4-Lie
  ⊛F4     : 𝕜 → F4-Lie → F4-Lie
  [_,_]₄  : F4-Lie → F4-Lie → F4-Lie

-- ================================================================
-- §2. トレース 0 の Jordan 代数元 𝔍ᶜ₀
-- ================================================================
record 𝔍ᶜ₀ : Type where
  constructor mk𝔍₀
  field
    element : 𝔍ᶜ
    is-trace0 : tr-𝔍 element ≡ 𝕜-zero

-- ================================================================
-- §3. E6 Lie 環の定義 (𝔢₆ = 𝔣₄ ⊕ 𝔍ᶜ₀)
-- ================================================================
record E6-Lie : Type where
  constructor mkE6
  field
    D  : F4-Lie  -- 𝔣₄ 部分
    A₀ : 𝔍ᶜ₀     -- 𝔍ᶜ₀ 部分

-- E6 の零元
E6-zero : E6-Lie
E6-zero = mkE6 F4-zero (mk𝔍₀ (mk𝔍 𝕜-zero 𝕜-zero 𝕜-zero 𝕆-zero 𝕆-zero 𝕆-zero) postulate-tr0)
  where postulate postulate-tr0 : _ ≡ 𝕜-zero

-- ================================================================
-- §3.5. E6 の線形構造
-- ================================================================
𝔍ᶜ₀-zero : 𝔍ᶜ₀
𝔍ᶜ₀-zero = mk𝔍₀ (mk𝔍 𝕜-zero 𝕜-zero 𝕜-zero 𝕆-zero 𝕆-zero 𝕆-zero) postulate-tr0
  where postulate postulate-tr0 : tr-𝔍 (mk𝔍 𝕜-zero 𝕜-zero 𝕜-zero 𝕆-zero 𝕆-zero 𝕆-zero) ≡ 𝕜-zero

postulate
  _+𝔍₀_   : 𝔍ᶜ₀ → 𝔍ᶜ₀ → 𝔍ᶜ₀
  -𝔍₀     : 𝔍ᶜ₀ → 𝔍ᶜ₀
  ⊛𝔍₀    : 𝕜 → 𝔍ᶜ₀ → 𝔍ᶜ₀

_+E6_ : E6-Lie → E6-Lie → E6-Lie
(mkE6 D1 A1) +E6 (mkE6 D2 A2) = mkE6 (D1 +F4 D2) (A1 +𝔍₀ A2)

-E6_ : E6-Lie → E6-Lie
-E6 (mkE6 D A) = mkE6 (-F4 D) (-𝔍₀ A)

_⊛E6_ : 𝕜 → E6-Lie → E6-Lie
k ⊛E6 (mkE6 D A) = mkE6 (⊛F4 k D) (⊛𝔍₀ k A)

infixl 20 _+E6_

-- ================================================================
-- §4. E6 の作用 phi-act (𝔢₆ から 𝔍ᶜ への作用)
-- ================================================================
-- ϕ = (D, A) に対して ϕ(X) = DX + A ∘ X
phi-act : E6-Lie → 𝔍ᶜ → 𝔍ᶜ
phi-act (mkE6 (mkF4 D _) (mk𝔍₀ A _)) X = D X +𝔍 (A ∘ X)

-- phi-adjoint-act: トレース形式 ⟨X,Y⟩=tr(X∘Y) に関する随伴
postulate
  phi-adjoint-act : E6-Lie → 𝔍ᶜ → 𝔍ᶜ

-- ================================================================
-- §5. E6 Lie 環の括弧積 [_,_]₆
-- ================================================================
-- 論文 source 85 等に基づき、(D, A) と (D', A') の積を定義する
-- [ (D, A), (D', A') ] = ( [D, D'] + [L_A, L_A'], D A' - D' A )
-- ここで [L_A, L_A'] は A ∨ A' (Jordan積の交換子) に相当する

-- ================================================================
-- §6. Jordan 導来 A ∨ B の実装
-- ================================================================
-- [L_A, L_B] X = A ∘ (B ∘ X) - B ∘ (A ∘ X)
jordan-deriv : 𝔍ᶜ → 𝔍ᶜ → F4-Lie
jordan-deriv A B = mkF4 deriv-func postulate-is-deriv
  where
    deriv-func : 𝔍ᶜ → 𝔍ᶜ
    deriv-func X = (A ∘ (B ∘ X)) +𝔍 (-𝔍 (B ∘ (A ∘ X)))

    postulate
      postulate-is-deriv : (X Y : 𝔍ᶜ) → deriv-func (X ∘ Y) ≡ (deriv-func X ∘ Y) +𝔍 (X ∘ deriv-func Y)

-- A ∨ B : Jordan 導来 [L_A, L_B] を E6 の元として表す
_∨𝔍_ : 𝔍ᶜ → 𝔍ᶜ → E6-Lie
A ∨𝔍 B = mkE6 (jordan-deriv A B) 𝔍ᶜ₀-zero

-- ================================================================
-- §7. E6 括弧積の具体的定義
-- ================================================================
concrete-bracket-E6 : E6-Lie → E6-Lie → E6-Lie
concrete-bracket-E6 (mkE6 D1 A1) (mkE6 D2 A2) = mkE6 D-res A-res
  where
    -- D-res = [D1, D2]₄ + (A1 ∨ A2)  [L_A, L_A'] に相当
    D-res : F4-Lie
    D-res = [ D1 , D2 ]₄ +F4 jordan-deriv (𝔍ᶜ₀.element A1) (𝔍ᶜ₀.element A2)

    -- A-res = D1(A2) - D2(A1)
    A-res : 𝔍ᶜ₀
    A-res = mk𝔍₀ elem postulate-tr0
      where
        elem : 𝔍ᶜ
        elem = (F4-Lie.deriv D1 (𝔍ᶜ₀.element A2)) +𝔍 (-𝔍 (F4-Lie.deriv D2 (𝔍ᶜ₀.element A1)))
        postulate postulate-tr0 : tr-𝔍 elem ≡ 𝕜-zero

[_,_]₆ : E6-Lie → E6-Lie → E6-Lie
[_,_]₆ = concrete-bracket-E6

infixl 20 _+F4_
infix  35 [_,_]₄
infix  35 [_,_]₆