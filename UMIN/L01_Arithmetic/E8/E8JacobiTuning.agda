{-# OPTIONS --cubical --guardedness #-}

-- ================================================================
-- E₈ Jacobi Tuning: P-Component Cyclic Sum & Coefficient Forcing
-- ================================================================

module UMIN.L01_Arithmetic.E8.E8JacobiTuning where

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
-- §1. E₇ Interface & Axioms
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

-- Fixity declarations
infixl 20 _+𝕜_ _+E7_ -E7_ _+P_ -P_
infixl 30 _·𝕜_ _⊛P_ _⊛E7_
infix  35 [_,_]₇
infix  40 _×F_

postulate
  E7-antisym : (Φ₁ Φ₂ : E7) → [ Φ₁ , Φ₂ ]₇ ≡ -E7 [ Φ₂ , Φ₁ ]₇
  E7-Jacobi : (Φ₁ Φ₂ Φ₃ : E7)
    → (([ Φ₁ , [ Φ₂ , Φ₃ ]₇ ]₇) +E7 ([ Φ₂ , [ Φ₃ , Φ₁ ]₇ ]₇) +E7 ([ Φ₃ , [ Φ₁ , Φ₂ ]₇ ]₇)) ≡ E7-zero
  ×F-derivation : (Φ : E7) (P Q : Pᶜ)
    → [ Φ , P ×F Q ]₇ ≡ ((E7-act Φ P) ×F Q) +E7 (P ×F (E7-act Φ Q))
  ⟨⟩-invariant : (Φ : E7) (P Q : Pᶜ)
    → ⟨ E7-act Φ P , Q ⟩ₛ +𝕜 ⟨ P , E7-act Φ Q ⟩ₛ ≡ 𝕜-zero
  E7-rep : (Φ₁ Φ₂ : E7) (P : Pᶜ)
    → E7-act [ Φ₁ , Φ₂ ]₇ P ≡ (E7-act Φ₁ (E7-act Φ₂ P)) +P (-P (E7-act Φ₂ (E7-act Φ₁ P)))
  ⟨⟩-antisym : (P Q : Pᶜ) → ⟨ P , Q ⟩ₛ ≡ -𝕜 ⟨ Q , P ⟩ₛ
  ×F-antisym : (P Q : Pᶜ) → P ×F Q ≡ -E7 (Q ×F P)

postulate
  +P-assoc   : (a b c : Pᶜ) → (a +P b) +P c ≡ a +P (b +P c)

-- ================================================================
-- §2. E₈ Structure
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

-- ================================================================
-- §3. Tuning Components (a) and (b)
-- ================================================================

Term-a : Pᶜ → Pᶜ → Pᶜ → Pᶜ
Term-a p₁ p₂ p₃ = (E7-act (p₁ ×F p₃) p₂) +P (-P (E7-act (p₂ ×F p₃) p₁))

Term-b : Pᶜ → Pᶜ → Pᶜ → Pᶜ
Term-b p₁ p₂ p₃ = (⟨ p₁ , p₃ ⟩ₛ ⊛P p₂) +P (-P (⟨ p₂ , p₃ ⟩ₛ ⊛P p₁))

postulate
  ×F-Jacobi-on-P : (p₁ p₂ p₃ : Pᶜ) → (Term-a p₁ p₂ p₃ +P Term-b p₁ p₂ p₃) ≡ Pᶜ-zero

-- ================================================================
-- §4. Coefficient Forcing (The Fixed Equations)
-- ================================================================

record KillingCoeffs : Type where
  constructor mkCoeffs
  field
    k₁ : ℚ⁺
    k₂ : ℚ⁺
    k₃ : ℚ⁺
open KillingCoeffs

miyashita-coeffs : KillingCoeffs
miyashita-coeffs = mkCoeffs (5 // 3) (15 // 1) (120 // 1)

postulate
  ratEmbed : ℚ⁺ → 𝕜 → 𝕜
  B₈ : KillingCoeffs → E8 → E8 → 𝕜
  AdInvariance : KillingCoeffs → Type

-- Here we fixed the type by grouping (num * 9) before making it a ℚ⁺
CoefficientForcing : Type
CoefficientForcing =
  (κ : KillingCoeffs)
  → AdInvariance κ
  → (k₂ κ) ≡ᵣ ((num (k₁ κ) · 9) // den (k₁ κ))

-- Final Ratio Proofs (grouping with parentheses to satisfy Agda)
proof-ratio-k₂/k₁ : num (k₂ miyashita-coeffs) · den (k₁ miyashita-coeffs)
                    ≡ (9 · num (k₁ miyashita-coeffs)) · den (k₂ miyashita-coeffs)
proof-ratio-k₂/k₁ = refl

proof-ratio-k₃/k₂ : num (k₃ miyashita-coeffs) · den (k₂ miyashita-coeffs)
                    ≡ (8 · num (k₂ miyashita-coeffs)) · den (k₃ miyashita-coeffs)
proof-ratio-k₃/k₂ = refl

distortion-δ : ℚ⁺
distortion-δ = 126 // 17

check-δ : 126 · 680 ≡ 17 · 5040
check-δ = refl