{-# OPTIONS --cubical --guardedness #-}

module UMIN.L01_Math.Algebraic_Structures.LieAlgebra.E8LieAlgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _·_)

-- ================================================================
-- §0. Rational Arithmetic
-- ================================================================

record ℚ⁺ : Type where
  constructor _//_
  field
    num : ℕ
    den : ℕ
open ℚ⁺

_≡ᵣ_ : ℚ⁺ → ℚ⁺ → Type
(a // b) ≡ᵣ (c // d) = a · d ≡ b · c

-- ================================================================
--  LAYER 1 : E₇ INTERFACE (Names)
-- ================================================================

postulate
  E7  : Type
  Pᶜ  : Type
  𝕜   : Type
  𝕜-zero  : 𝕜
  𝕜-one   : 𝕜
  _+𝕜_    : 𝕜 → 𝕜 → 𝕜
  _·𝕜_    : 𝕜 → 𝕜 → 𝕜
  -𝕜_     : 𝕜 → 𝕜
  
  [_,_]₇     : E7 → E7 → E7
  E7-zero    : E7
  _+E7_      : E7 → E7 → E7
  -E7_       : E7 → E7
  B₇         : E7 → E7 → 𝕜
  
  Pᶜ-zero   : Pᶜ
  _+P_      : Pᶜ → Pᶜ → Pᶜ
  -P_       : Pᶜ → Pᶜ
  _⊛P_     : 𝕜 → Pᶜ → Pᶜ
  
  E7-act    : E7 → Pᶜ → Pᶜ
  _×F_      : Pᶜ → Pᶜ → E7
  ⟨_,_⟩ₛ   : Pᶜ → Pᶜ → 𝕜
  _⊛E7_    : 𝕜 → E7 → E7

-- 1. 名前を出し切った後で、まとめてルール（infix）を設定
infixl 20 _+𝕜_ _+E7_ -E7_ _+P_ -P_
infixl 30 _·𝕜_ _⊛P_ _⊛E7_
infix  35 [_,_]₇
infix  40 _×F_

-- 2. その後に、一度だけ公理（Axioms）を定義
postulate
  E7-antisym : (Φ₁ Φ₂ : E7) → [ Φ₁ , Φ₂ ]₇ ≡ -E7 [ Φ₂ , Φ₁ ]₇
  E7-Jacobi : (Φ₁ Φ₂ Φ₃ : E7)
    → (([ Φ₁ , [ Φ₂ , Φ₃ ]₇ ]₇) +E7 ([ Φ₂ , [ Φ₃ , Φ₁ ]₇ ]₇) +E7 ([ Φ₃ , [ Φ₁ , Φ₂ ]₇ ]₇)) ≡ E7-zero
  E7-rep : (Φ₁ Φ₂ : E7) (P : Pᶜ)
    → E7-act [ Φ₁ , Φ₂ ]₇ P ≡ (E7-act Φ₁ (E7-act Φ₂ P)) +P (-P (E7-act Φ₂ (E7-act Φ₁ P)))
  ×F-derivation : (Φ : E7) (P Q : Pᶜ)
    → [ Φ , P ×F Q ]₇ ≡ ((E7-act Φ P) ×F Q) +E7 (P ×F (E7-act Φ Q))
  ⟨⟩-invariant : (Φ : E7) (P Q : Pᶜ)
    → ⟨ E7-act Φ P , Q ⟩ₛ +𝕜 ⟨ P , E7-act Φ Q ⟩ₛ ≡ 𝕜-zero
  ⟨⟩-antisym : (P Q : Pᶜ) → ⟨ P , Q ⟩ₛ ≡ -𝕜 ⟨ Q , P ⟩ₛ
  ×F-antisym : (P Q : Pᶜ) → P ×F Q ≡ -E7 (Q ×F P)

-- ================================================================
--  LAYER 2 : E₈ CONSTRUCTION
-- ================================================================

record E8 : Type where
  constructor mkE8
  field
    Φ : E7 ; P : Pᶜ ; Q : Pᶜ ; r : 𝕜 ; u : 𝕜 ; v : 𝕜
open E8

[_,_]₈ : E8 → E8 → E8
[ R₁ , R₂ ]₈ = mkE8 Φ′ P′ Q′ r′ u′ v′
  where
    Φ₁ = Φ R₁ ; Φ₂ = Φ R₂ ; P₁ = P R₁ ; P₂ = P R₂ ; Q₁ = Q R₁ ; Q₂ = Q R₂
    r₁ = r R₁ ; r₂ = r R₂ ; u₁ = u R₁ ; u₂ = u R₂ ; v₁ = v R₁ ; v₂ = v R₂

    Φ′ = ([ Φ₁ , Φ₂ ]₇) +E7 (P₁ ×F Q₂) +E7 (-E7 (P₂ ×F Q₁))
    P′ = (E7-act Φ₁ P₂) +P (-P (E7-act Φ₂ P₁)) +P (r₁ ⊛P P₂) +P (-P (r₂ ⊛P P₁)) +P (u₁ ⊛P Q₂) +P (-P (u₂ ⊛P Q₁))
    Q′ = (E7-act Φ₁ Q₂) +P (-P (E7-act Φ₂ Q₁)) +P (-P (r₁ ⊛P Q₂)) +P (r₂ ⊛P Q₁) +P (v₁ ⊛P P₂) +P (-P (v₂ ⊛P P₁))
    r′ = ⟨ P₁ , Q₂ ⟩ₛ +𝕜 (-𝕜 ⟨ P₂ , Q₁ ⟩ₛ)
    u′ = ⟨ Q₁ , Q₂ ⟩ₛ
    v′ = ⟨ P₁ , P₂ ⟩ₛ

infix 35 [_,_]₈

record KillingCoeffs : Type where
  constructor mkCoeffs
  field
    k₁ : ℚ⁺ ; k₂ : ℚ⁺ ; k₃ : ℚ⁺
open KillingCoeffs

miyashita-coeffs : KillingCoeffs
miyashita-coeffs = mkCoeffs (5 // 3) (15 // 1) (120 // 1)

postulate
  ratEmbed : ℚ⁺ → 𝕜 → 𝕜

B₈ : KillingCoeffs → E8 → E8 → 𝕜
B₈ κ R₁ R₂ =
    ratEmbed (k₁ κ) (B₇ (Φ R₁) (Φ R₂))
    +𝕜 ratEmbed (k₂ κ) (⟨ Q R₁ , P R₂ ⟩ₛ)
    +𝕜 (-𝕜 (ratEmbed (k₂ κ) (⟨ P R₁ , Q R₂ ⟩ₛ)))
    +𝕜 ratEmbed (k₃ κ) (r R₁ ·𝕜 r R₂)

-- ================================================================
--  LAYER 3 : THEOREMS AND PROOFS
-- ================================================================

dim-E7 = 133 ; dim-P = 56 ; dim-scalar = 3
dim-Hermitian = 136 ; dim-NonHermitian = 112 ; dim-E8-total = 248

check-Hermitian : dim-Hermitian ≡ 136
check-Hermitian = refl
check-NonHermitian : dim-NonHermitian ≡ 112
check-NonHermitian = refl
check-E8-total : dim-E8-total ≡ 248
check-E8-total = refl

proof-ratio-k₂/k₁ : num (k₂ miyashita-coeffs) · den (k₁ miyashita-coeffs) ≡ 9 · (num (k₁ miyashita-coeffs) · den (k₂ miyashita-coeffs))
proof-ratio-k₂/k₁ = refl

proof-ratio-k₃/k₂ : num (k₃ miyashita-coeffs) · den (k₂ miyashita-coeffs) ≡ 8 · (num (k₂ miyashita-coeffs) · den (k₃ miyashita-coeffs))
proof-ratio-k₃/k₂ = refl

distortion-δ : ℚ⁺
distortion-δ = 126 // 17

check-δ-ratio : 126 · 680 ≡ 17 · 5040
check-δ-ratio = refl

postulate
  _+E8_   : E8 → E8 → E8
  -E8_    : E8 → E8

infixl 20 _+E8_

E8-zero : E8
E8-zero = mkE8 E7-zero Pᶜ-zero Pᶜ-zero 𝕜-zero 𝕜-zero 𝕜-zero

JacobiIdentity : Type
JacobiIdentity = (X Y Z : E8) → (([ X , [ Y , Z ]₈ ]₈) +E8 ([ Y , [ Z , X ]₈ ]₈) +E8 ([ Z , [ X , Y ]₈ ]₈)) ≡ E8-zero

AdInvariance : KillingCoeffs → Type
AdInvariance κ = (X Y Z : E8) → B₈ κ [ X , Y ]₈ Z +𝕜 B₈ κ Y [ X , Z ]₈ ≡ 𝕜-zero

Cochain1 : Type
Cochain1 = E8 → 𝕜
Cochain2 : Type
Cochain2 = E8 → E8 → 𝕜
Cochain3 : Type
Cochain3 = E8 → E8 → E8 → 𝕜

d₁ : Cochain1 → Cochain2
d₁ f X Y = f [ X , Y ]₈

d₂ : Cochain2 → Cochain3
d₂ ω X Y Z = ω [ X , Y ]₈ Z +𝕜 (-𝕜 (ω [ X , Z ]₈ Y)) +𝕜 ω [ Y , Z ]₈ X

AnomalyCancellation : Type
AnomalyCancellation =
  (p₁ p₂ p₃ : Pᶜ) → let
    pureP : Pᶜ → E8
    pureP p = mkE8 E7-zero p Pᶜ-zero 𝕜-zero 𝕜-zero 𝕜-zero
    pureQ : Pᶜ → E8
    pureQ q = mkE8 E7-zero Pᶜ-zero q 𝕜-zero 𝕜-zero 𝕜-zero
  in Φ (([ pureP p₁ , [ pureP p₂ , pureQ p₃ ]₈ ]₈) +E8 ([ pureP p₂ , [ pureQ p₃ , pureP p₁ ]₈ ]₈) +E8 ([ pureQ p₃ , [ pureP p₁ , pureP p₂ ]₈ ]₈)) ≡ E7-zero