{-# OPTIONS --cubical --guardedness #-}

-- ================================================================
-- E₈ Anomaly Cancellation Phase 2:
-- P/r Component Analysis & Zero Simplification Proofs
-- ================================================================
--
-- 宮下先生の指示:
--   「Φ成分の安定確認は完了。次は、P成分および r成分における
--    非自明な相殺（カオスの調律）に移行せよ。」
--
-- This file:
--   §A. Proves P-of-bracket-PQ etc. (removing postulates)
--   §B. Computes outer bracket P-components (where ×F-derivation acts)
--   §C. Analyzes r-component (where δ = 126/17 enters)
--
-- The key discovery: when two pure distortion elements bracket,
-- P and Q components vanish. But in the OUTER bracket, the
-- P-component picks up terms like E7-act(p₂ ×F p₃)(p₁) and
-- ⟨p₂,p₃⟩⊛p₁ — THIS is where anomaly cancellation becomes
-- non-trivial and requires ×F-derivation to resolve.

module UMIN.L01_Math.Algebraic_Structures.LieAlgebra.E8AnomalyPhase2 where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _·_)

-- ================================================================
-- §0. E₇ Interface (reproduced, self-contained)
-- ================================================================

record ℚ⁺ : Type where
  constructor _//_
  field
    num : ℕ
    den : ℕ
open ℚ⁺

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

infixl 20 _+𝕜_ _+E7_ -E7_ _+P_ -P_
infixl 30 _·𝕜_ _⊛P_ _⊛E7_
infix  35 [_,_]₇
infix  40 _×F_

postulate
  -- E₇ axioms
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

  -- Algebraic laws
  +E7-assoc : (a b c : E7) → (a +E7 b) +E7 c ≡ a +E7 (b +E7 c)
  +E7-comm  : (a b : E7) → a +E7 b ≡ b +E7 a
  +E7-unitʳ : (a : E7) → a +E7 E7-zero ≡ a
  +E7-unitˡ : (a : E7) → E7-zero +E7 a ≡ a
  +E7-invʳ  : (a : E7) → a +E7 (-E7 a) ≡ E7-zero
  +E7-invˡ  : (a : E7) → (-E7 a) +E7 a ≡ E7-zero

  +P-assoc  : (a b c : Pᶜ) → (a +P b) +P c ≡ a +P (b +P c)
  +P-comm   : (a b : Pᶜ) → a +P b ≡ b +P a
  +P-unitˡ  : (a : Pᶜ) → Pᶜ-zero +P a ≡ a
  +P-unitʳ  : (a : Pᶜ) → a +P Pᶜ-zero ≡ a
  +P-invˡ   : (a : Pᶜ) → (-P a) +P a ≡ Pᶜ-zero
  +P-invʳ   : (a : Pᶜ) → a +P (-P a) ≡ Pᶜ-zero
  -P-zero   : -P Pᶜ-zero ≡ Pᶜ-zero

  ⊛P-zero  : (p : Pᶜ) → 𝕜-zero ⊛P p ≡ Pᶜ-zero
  ⊛E7-zero : (φ : E7) → 𝕜-zero ⊛E7 φ ≡ E7-zero

  E7-act-zero    : (Φ : E7) → E7-act Φ Pᶜ-zero ≡ Pᶜ-zero
  E7-act-by-zero : (p : Pᶜ) → E7-act E7-zero p ≡ Pᶜ-zero

  ×F-zeroˡ : (q : Pᶜ) → Pᶜ-zero ×F q ≡ E7-zero
  ×F-zeroʳ : (p : Pᶜ) → p ×F Pᶜ-zero ≡ E7-zero

  ⟨⟩-zeroˡ : (q : Pᶜ) → ⟨ Pᶜ-zero , q ⟩ₛ ≡ 𝕜-zero
  ⟨⟩-zeroʳ : (p : Pᶜ) → ⟨ p , Pᶜ-zero ⟩ₛ ≡ 𝕜-zero

  -E7-distrib-+E7 : (a b : E7) → -E7 (a +E7 b) ≡ (-E7 a) +E7 (-E7 b)
  -E7-invol  : (a : E7) → -E7 (-E7 a) ≡ a
  -E7-zero   : -E7 E7-zero ≡ E7-zero

  [,]₇-zeroˡ : (Φ : E7) → [ E7-zero , Φ ]₇ ≡ E7-zero
  [,]₇-zeroʳ : (Φ : E7) → [ Φ , E7-zero ]₇ ≡ E7-zero

  +𝕜-unitˡ : (x : 𝕜) → 𝕜-zero +𝕜 x ≡ x
  +𝕜-unitʳ : (x : 𝕜) → x +𝕜 𝕜-zero ≡ x
  -𝕜-zero  : -𝕜 𝕜-zero ≡ 𝕜-zero


-- ================================================================
-- §1. E₈ Record and Bracket
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

E8-zero : E8
E8-zero = mkE8 E7-zero Pᶜ-zero Pᶜ-zero 𝕜-zero 𝕜-zero 𝕜-zero

pureP : Pᶜ → E8
pureP p = mkE8 E7-zero p Pᶜ-zero 𝕜-zero 𝕜-zero 𝕜-zero

pureQ : Pᶜ → E8
pureQ q = mkE8 E7-zero Pᶜ-zero q 𝕜-zero 𝕜-zero 𝕜-zero


-- ================================================================
--     ╔══════════════════════════════════════════════════╗
--     ║  PART A: Zero Simplification Proofs              ║
--     ║  (Removing postulates from Phase 1)              ║
--     ╚══════════════════════════════════════════════════╝
-- ================================================================

-- ================================================================
-- §A.1  Helper: 6-fold Pᶜ-zero simplification
-- ================================================================
-- The P-component of [pureP p, pureQ q]₈ expands to:
--
--   E7-act(0, 0) +P (-P(E7-act(0, p)))
--   +P (0 ⊛P 0)  +P (-P(0 ⊛P p))
--   +P (0 ⊛P q)  +P (-P(0 ⊛P 0))
--
-- where the arguments are:
--   Φ₁=0, Φ₂=0, P₁=p, P₂=0, Q₁=0, Q₂=q
--   r₁=0, r₂=0, u₁=0, u₂=0, v₁=0, v₂=0
--
-- Each of the 6 terms reduces to Pᶜ-zero.

-- Individual term lemmas:
private
  -- E7-act(E7-zero, Pᶜ-zero) = Pᶜ-zero
  t1-PQ : (p q : Pᶜ) → E7-act E7-zero Pᶜ-zero ≡ Pᶜ-zero
  t1-PQ _ _ = E7-act-by-zero Pᶜ-zero

  -- -P(E7-act(E7-zero, p)) = -P(Pᶜ-zero) = Pᶜ-zero
  t2-PQ : (p q : Pᶜ) → -P (E7-act E7-zero p) ≡ Pᶜ-zero
  t2-PQ p _ = cong -P_ (E7-act-by-zero p) ∙ -P-zero

  -- 𝕜-zero ⊛P Pᶜ-zero = Pᶜ-zero
  t3-PQ : (p q : Pᶜ) → 𝕜-zero ⊛P Pᶜ-zero ≡ Pᶜ-zero
  t3-PQ _ _ = ⊛P-zero Pᶜ-zero

  -- -P(𝕜-zero ⊛P p) = -P(Pᶜ-zero) = Pᶜ-zero
  t4-PQ : (p q : Pᶜ) → -P (𝕜-zero ⊛P p) ≡ Pᶜ-zero
  t4-PQ p _ = cong -P_ (⊛P-zero p) ∙ -P-zero

  -- 𝕜-zero ⊛P q = Pᶜ-zero
  t5-PQ : (p q : Pᶜ) → 𝕜-zero ⊛P q ≡ Pᶜ-zero
  t5-PQ _ q = ⊛P-zero q

  -- -P(𝕜-zero ⊛P Pᶜ-zero) = Pᶜ-zero
  t6-PQ : (p q : Pᶜ) → -P (𝕜-zero ⊛P Pᶜ-zero) ≡ Pᶜ-zero
  t6-PQ _ _ = cong -P_ (⊛P-zero Pᶜ-zero) ∙ -P-zero


-- §A.2  Chain collapse: sum of 6 zeros = zero
-- We need: 0 +P 0 +P 0 +P 0 +P 0 +P 0 = 0
-- Strategy: collapse from left, using +P-unitˡ repeatedly.

six-zeros-P : Pᶜ-zero +P Pᶜ-zero +P Pᶜ-zero +P Pᶜ-zero +P Pᶜ-zero +P Pᶜ-zero ≡ Pᶜ-zero
six-zeros-P =
    cong (_+P Pᶜ-zero) (cong (_+P Pᶜ-zero) (cong (_+P Pᶜ-zero) (cong (_+P Pᶜ-zero)
      (+P-unitˡ Pᶜ-zero))))
  ∙ cong (_+P Pᶜ-zero) (cong (_+P Pᶜ-zero) (cong (_+P Pᶜ-zero)
      (+P-unitˡ Pᶜ-zero)))
  ∙ cong (_+P Pᶜ-zero) (cong (_+P Pᶜ-zero)
      (+P-unitˡ Pᶜ-zero))
  ∙ cong (_+P Pᶜ-zero)
      (+P-unitˡ Pᶜ-zero)
  ∙ +P-unitˡ Pᶜ-zero


-- ================================================================
-- §A.3  THEOREM: P-of-bracket-PQ (previously postulated)
-- ================================================================
-- P [pureP p, pureQ q]₈ ≡ Pᶜ-zero

P-of-bracket-PQ : (p q : Pᶜ)
  → P [ pureP p , pureQ q ]₈ ≡ Pᶜ-zero
P-of-bracket-PQ p q =
  -- P [pureP p, pureQ q]₈ definitionally equals:
  -- E7-act(0, 0) +P (-P(E7-act(0, p))) +P (0⊛0) +P (-P(0⊛p)) +P (0⊛q) +P (-P(0⊛0))
  --
  -- Rewrite each of the 6 terms to Pᶜ-zero, then collapse.
  cong₂ (λ a b → a +P b +P (𝕜-zero ⊛P Pᶜ-zero) +P (-P (𝕜-zero ⊛P p)) +P (𝕜-zero ⊛P q) +P (-P (𝕜-zero ⊛P Pᶜ-zero)))
    (t1-PQ p q) (t2-PQ p q)
  ∙ cong₂ (λ a b → Pᶜ-zero +P Pᶜ-zero +P a +P b +P (𝕜-zero ⊛P q) +P (-P (𝕜-zero ⊛P Pᶜ-zero)))
      (t3-PQ p q) (t4-PQ p q)
  ∙ cong₂ (λ a b → Pᶜ-zero +P Pᶜ-zero +P Pᶜ-zero +P Pᶜ-zero +P a +P b)
      (t5-PQ p q) (t6-PQ p q)
  ∙ six-zeros-P


-- ================================================================
-- §A.4  THEOREM: Q-of-bracket-PQ (previously postulated)
-- ================================================================
-- Q [pureP p, pureQ q]₈
-- Q-component formula with Φ₁=0, Φ₂=0, Q₁=0, Q₂=q, P₁=p, P₂=0:
--   E7-act(0, q) +P (-P(E7-act(0, 0))) +P (-P(0⊛q)) +P (0⊛0)
--   +P (0⊛0) +P (-P(0⊛p))

private
  -- E7-act(E7-zero, q) = Pᶜ-zero
  q1-PQ : (p q : Pᶜ) → E7-act E7-zero q ≡ Pᶜ-zero
  q1-PQ _ q = E7-act-by-zero q

  -- -P(E7-act(E7-zero, Pᶜ-zero)) = Pᶜ-zero
  q2-PQ : (p q : Pᶜ) → -P (E7-act E7-zero Pᶜ-zero) ≡ Pᶜ-zero
  q2-PQ _ _ = cong -P_ (E7-act-by-zero Pᶜ-zero) ∙ -P-zero

  -- -P(𝕜-zero ⊛P q) = Pᶜ-zero
  q3-PQ : (p q : Pᶜ) → -P (𝕜-zero ⊛P q) ≡ Pᶜ-zero
  q3-PQ _ q = cong -P_ (⊛P-zero q) ∙ -P-zero

  -- 𝕜-zero ⊛P Pᶜ-zero = Pᶜ-zero
  q4-PQ : (p q : Pᶜ) → 𝕜-zero ⊛P Pᶜ-zero ≡ Pᶜ-zero
  q4-PQ _ _ = ⊛P-zero Pᶜ-zero

  -- 𝕜-zero ⊛P Pᶜ-zero = Pᶜ-zero  (v₁ ⊛P P₂)
  q5-PQ : (p q : Pᶜ) → 𝕜-zero ⊛P Pᶜ-zero ≡ Pᶜ-zero
  q5-PQ _ _ = ⊛P-zero Pᶜ-zero

  -- -P(𝕜-zero ⊛P p) = Pᶜ-zero
  q6-PQ : (p q : Pᶜ) → -P (𝕜-zero ⊛P p) ≡ Pᶜ-zero
  q6-PQ p _ = cong -P_ (⊛P-zero p) ∙ -P-zero


Q-of-bracket-PQ : (p q : Pᶜ)
  → Q [ pureP p , pureQ q ]₈ ≡ Pᶜ-zero
Q-of-bracket-PQ p q =
  cong₂ (λ a b → a +P b +P (-P (𝕜-zero ⊛P q)) +P (𝕜-zero ⊛P Pᶜ-zero) +P (𝕜-zero ⊛P Pᶜ-zero) +P (-P (𝕜-zero ⊛P p)))
    (q1-PQ p q) (q2-PQ p q)
  ∙ cong₂ (λ a b → Pᶜ-zero +P Pᶜ-zero +P a +P b +P (𝕜-zero ⊛P Pᶜ-zero) +P (-P (𝕜-zero ⊛P p)))
      (q3-PQ p q) (q4-PQ p q)
  ∙ cong₂ (λ a b → Pᶜ-zero +P Pᶜ-zero +P Pᶜ-zero +P Pᶜ-zero +P a +P b)
      (q5-PQ p q) (q6-PQ p q)
  ∙ six-zeros-P


-- ================================================================
-- §A.5  P,Q vanishing for [pureQ q, pureP p] and [pureP, pureP]
-- ================================================================
-- Same technique: expand, show each term is Pᶜ-zero, collapse.
-- For [pureQ q, pureP p]: Φ₁=0, Φ₂=0, P₁=0, P₂=p, Q₁=q, Q₂=0
-- For [pureP p₁, pureP p₂]: Φ₁=0, Φ₂=0, P₁=p₁, P₂=p₂, Q₁=0, Q₂=0

P-of-bracket-QP : (q p : Pᶜ)
  → P [ pureQ q , pureP p ]₈ ≡ Pᶜ-zero
P-of-bracket-QP q p =
  -- P-component: E7-act(0,p) +P (-P(E7-act(0,0))) +P (0⊛p) +P (-P(0⊛0)) +P (0⊛0) +P (-P(0⊛q))
  cong₂ (λ a b → a +P b +P (𝕜-zero ⊛P p) +P (-P (𝕜-zero ⊛P Pᶜ-zero)) +P (𝕜-zero ⊛P Pᶜ-zero) +P (-P (𝕜-zero ⊛P q)))
    (E7-act-by-zero p) (cong -P_ (E7-act-by-zero Pᶜ-zero) ∙ -P-zero)
  ∙ cong₂ (λ a b → Pᶜ-zero +P Pᶜ-zero +P a +P b +P (𝕜-zero ⊛P Pᶜ-zero) +P (-P (𝕜-zero ⊛P q)))
      (⊛P-zero p) (cong -P_ (⊛P-zero Pᶜ-zero) ∙ -P-zero)
  ∙ cong₂ (λ a b → Pᶜ-zero +P Pᶜ-zero +P Pᶜ-zero +P Pᶜ-zero +P a +P b)
      (⊛P-zero Pᶜ-zero) (cong -P_ (⊛P-zero q) ∙ -P-zero)
  ∙ six-zeros-P


Q-of-bracket-QP : (q p : Pᶜ)
  → Q [ pureQ q , pureP p ]₈ ≡ Pᶜ-zero
Q-of-bracket-QP q p =
  -- Q-component: E7-act(0,0) +P (-P(E7-act(0,q))) +P (-P(0⊛0)) +P (0⊛q) +P (0⊛p) +P (-P(0⊛0))
  cong₂ (λ a b → a +P b +P (-P (𝕜-zero ⊛P Pᶜ-zero)) +P (𝕜-zero ⊛P q) +P (𝕜-zero ⊛P p) +P (-P (𝕜-zero ⊛P Pᶜ-zero)))
    (E7-act-by-zero Pᶜ-zero) (cong -P_ (E7-act-by-zero q) ∙ -P-zero)
  ∙ cong₂ (λ a b → Pᶜ-zero +P Pᶜ-zero +P a +P b +P (𝕜-zero ⊛P p) +P (-P (𝕜-zero ⊛P Pᶜ-zero)))
      (cong -P_ (⊛P-zero Pᶜ-zero) ∙ -P-zero) (⊛P-zero q)
  ∙ cong₂ (λ a b → Pᶜ-zero +P Pᶜ-zero +P Pᶜ-zero +P Pᶜ-zero +P a +P b)
      (⊛P-zero p) (cong -P_ (⊛P-zero Pᶜ-zero) ∙ -P-zero)
  ∙ six-zeros-P


P-of-bracket-PP : (p₁ p₂ : Pᶜ)
  → P [ pureP p₁ , pureP p₂ ]₈ ≡ Pᶜ-zero
P-of-bracket-PP p₁ p₂ =
  -- P₁=p₁, P₂=p₂, Q₁=Q₂=0, all scalars 0
  -- P-component: E7-act(0,p₂) +P (-P(E7-act(0,p₁))) +P (0⊛p₂) +P (-P(0⊛p₁)) +P (0⊛0) +P (-P(0⊛0))
  cong₂ (λ a b → a +P b +P (𝕜-zero ⊛P p₂) +P (-P (𝕜-zero ⊛P p₁)) +P (𝕜-zero ⊛P Pᶜ-zero) +P (-P (𝕜-zero ⊛P Pᶜ-zero)))
    (E7-act-by-zero p₂) (cong -P_ (E7-act-by-zero p₁) ∙ -P-zero)
  ∙ cong₂ (λ a b → Pᶜ-zero +P Pᶜ-zero +P a +P b +P (𝕜-zero ⊛P Pᶜ-zero) +P (-P (𝕜-zero ⊛P Pᶜ-zero)))
      (⊛P-zero p₂) (cong -P_ (⊛P-zero p₁) ∙ -P-zero)
  ∙ cong₂ (λ a b → Pᶜ-zero +P Pᶜ-zero +P Pᶜ-zero +P Pᶜ-zero +P a +P b)
      (⊛P-zero Pᶜ-zero) (cong -P_ (⊛P-zero Pᶜ-zero) ∙ -P-zero)
  ∙ six-zeros-P


Q-of-bracket-PP : (p₁ p₂ : Pᶜ)
  → Q [ pureP p₁ , pureP p₂ ]₈ ≡ Pᶜ-zero
Q-of-bracket-PP p₁ p₂ =
  -- Q₁=Q₂=0, P₁=p₁, P₂=p₂
  -- Q-component: E7-act(0,0) +P (-P(E7-act(0,0))) +P (-P(0⊛0)) +P (0⊛0) +P (0⊛p₂) +P (-P(0⊛p₁))
  cong₂ (λ a b → a +P b +P (-P (𝕜-zero ⊛P Pᶜ-zero)) +P (𝕜-zero ⊛P Pᶜ-zero) +P (𝕜-zero ⊛P p₂) +P (-P (𝕜-zero ⊛P p₁)))
    (E7-act-by-zero Pᶜ-zero) (cong -P_ (E7-act-by-zero Pᶜ-zero) ∙ -P-zero)
  ∙ cong₂ (λ a b → Pᶜ-zero +P Pᶜ-zero +P a +P b +P (𝕜-zero ⊛P p₂) +P (-P (𝕜-zero ⊛P p₁)))
      (cong -P_ (⊛P-zero Pᶜ-zero) ∙ -P-zero) (⊛P-zero Pᶜ-zero)
  ∙ cong₂ (λ a b → Pᶜ-zero +P Pᶜ-zero +P Pᶜ-zero +P Pᶜ-zero +P a +P b)
      (⊛P-zero p₂) (cong -P_ (⊛P-zero p₁) ∙ -P-zero)
  ∙ six-zeros-P


-- ================================================================
--     ╔══════════════════════════════════════════════════╗
--     ║  PART B: Outer Bracket P-Component Analysis      ║
--     ║  (Where ×F-derivation enters the picture)        ║
--     ╚══════════════════════════════════════════════════╝
-- ================================================================

-- ================================================================
-- §B.1  P-component of [pureP p₁, M]₈  where M = [pureP p₂, pureQ p₃]₈
-- ================================================================
--
-- M has: Φ(M) = p₂ ×F p₃,  P(M) = 0,  Q(M) = 0,
--        r(M) = ⟨p₂,p₃⟩ₛ,  u(M) = 0,  v(M) = 0
--
-- [pureP p₁, M]₈ P-component:
--   Φ₁ = 0, Φ₂ = p₂ ×F p₃
--   P₁ = p₁, P₂ = 0
--   Q₁ = 0, Q₂ = 0
--   r₁ = 0, r₂ = ⟨p₂,p₃⟩ₛ
--   u₁ = 0, u₂ = 0
--   v₁ = 0, v₂ = 0
--
-- P′ = E7-act(0, 0)                    -- term 1: 0
--      +P (-P(E7-act(p₂×Fp₃, p₁)))    -- term 2: ★ NON-ZERO
--      +P (0 ⊛P 0)                     -- term 3: 0
--      +P (-P(⟨p₂,p₃⟩ₛ ⊛P p₁))       -- term 4: ★ NON-ZERO
--      +P (0 ⊛P 0)                     -- term 5: 0
--      +P (-P(0 ⊛P 0))                 -- term 6: 0
--
-- Simplified:
--   P′ = -P(E7-act(p₂ ×F p₃)(p₁)) +P (-P(⟨p₂,p₃⟩ₛ ⊛P p₁))
--
-- THIS is the non-trivial content:
--   Term A: E₇ core (p₂ ×F p₃) rotating p₁ via adjoint action
--   Term B: Scalar coupling ⟨p₂,p₃⟩ₛ scaling p₁
--
-- For the Jacobi identity on P-components, the cyclic sum of
-- three such expressions must vanish. This is where ×F-derivation
-- and the symplectic pairing ⟨⟩-invariant play their roles.

-- Type alias for readability
P-outer-1-expected : Pᶜ → Pᶜ → Pᶜ → Pᶜ
P-outer-1-expected p₁ p₂ p₃ =
  (-P (E7-act (p₂ ×F p₃) p₁)) +P (-P (⟨ p₂ , p₃ ⟩ₛ ⊛P p₁))


-- ================================================================
-- §B.2  Summary: Non-trivial P-components of outer brackets
-- ================================================================
--
-- Term 1: P[pureP p₁, [pureP p₂, pureQ p₃]₈]₈
--   = -P(E7-act(p₂ ×F p₃)(p₁)) +P (-P(⟨p₂,p₃⟩ₛ ⊛P p₁))
--
-- Term 2: P[pureP p₂, [pureQ p₃, pureP p₁]₈]₈
--   Inner: Φ = -E7(p₁ ×F p₃),  r = ⟨0,p₁⟩ₛ - ⟨p,0⟩ₛ = ...
--   (More complex — requires careful tracking)
--
-- Term 3: P[pureQ p₃, [pureP p₁, pureP p₂]₈]₈
--   Inner: Φ = E7-zero, r = ⟨p₁,0⟩ₛ - ⟨p₂,0⟩ₛ = 0
--   (Simpler — Φ=0 means no E7-act contribution)
--
-- The CYCLIC SUM of these three P-components must vanish.
-- This is where the real anomaly cancellation happens,
-- mediated by ×F-derivation and ⟨⟩-invariant.


-- ================================================================
--     ╔══════════════════════════════════════════════════╗
--     ║  PART C: r-Component & δ = 126/17 Connection     ║
--     ╚══════════════════════════════════════════════════╝
-- ================================================================

-- ================================================================
-- §C.1  r-component of inner brackets
-- ================================================================
--
-- [pureP p, pureQ q]₈ .r = ⟨p,q⟩ₛ         (proved in Phase 1)
-- [pureQ q, pureP p]₈ .r = ⟨0,0⟩ₛ - ⟨p,q⟩ₛ = -⟨p,q⟩ₛ
-- [pureP p₁, pureP p₂]₈ .r = ⟨p₁,0⟩ₛ - ⟨p₂,0⟩ₛ = 0

r-of-bracket-QP : (q p : Pᶜ)
  → r [ pureQ q , pureP p ]₈ ≡ -𝕜 ⟨ p , q ⟩ₛ
r-of-bracket-QP q p =
  -- r = ⟨P₁,Q₂⟩ₛ +𝕜 (-𝕜 ⟨P₂,Q₁⟩ₛ)
  -- P₁=Pᶜ-zero, Q₂=Pᶜ-zero, P₂=p, Q₁=q
  -- = ⟨0,0⟩ₛ +𝕜 (-𝕜 ⟨p,q⟩ₛ)
  -- = 0 +𝕜 (-𝕜 ⟨p,q⟩ₛ)
  -- = -𝕜 ⟨p,q⟩ₛ
  cong (_+𝕜 (-𝕜 ⟨ p , q ⟩ₛ)) (⟨⟩-zeroˡ Pᶜ-zero)
  ∙ +𝕜-unitˡ (-𝕜 ⟨ p , q ⟩ₛ)


r-of-bracket-PP : (p₁ p₂ : Pᶜ)
  → r [ pureP p₁ , pureP p₂ ]₈ ≡ 𝕜-zero
r-of-bracket-PP p₁ p₂ =
  -- r = ⟨p₁,0⟩ₛ +𝕜 (-𝕜 ⟨p₂,0⟩ₛ)
  -- = 0 +𝕜 (-𝕜 0)
  -- = 0 +𝕜 0 = 0
  cong₂ (λ a b → a +𝕜 (-𝕜 b)) (⟨⟩-zeroʳ p₁) (⟨⟩-zeroʳ p₂)
  ∙ cong (𝕜-zero +𝕜_) -𝕜-zero
  ∙ +𝕜-unitˡ 𝕜-zero


-- ================================================================
-- §C.2  The distortion factor in context
-- ================================================================
--
-- The r-component of the outer bracket [pureP p₁, M]₈ where
-- M = [pureP p₂, pureQ p₃]₈ is:
--
--   r′ = ⟨p₁, Q(M)⟩ₛ +𝕜 (-𝕜 ⟨P(M), 0⟩ₛ)
--      = ⟨p₁, 0⟩ₛ +𝕜 (-𝕜 ⟨0, 0⟩ₛ)   (since P(M)=Q(M)=0)
--      = 0
--
-- So the r-component of each outer double bracket also vanishes!
-- The scalar coupling ⟨p₂,p₃⟩ₛ from the inner bracket enters
-- only through the P-component (as ⟨p₂,p₃⟩ₛ ⊛P p₁).
--
-- This means δ = 126/17 enters the picture at the NEXT level:
-- when we consider Jacobi on MIXED elements (not purely P/Q),
-- or when we examine how the Killing form B₈ weights the
-- different components in its ad-invariance condition.
--
-- The connection is:
--   AdInvariance: B₈([X,Y], Z) + B₈(Y, [X,Z]) = 0
--   This equation, when expanded with parametric coefficients
--   (k₁, k₂, k₃), forces k₂/k₁ = 9 and k₃/k₂ = 8.
--   The distortion factor δ = (k₂ · 112) / (k₁ · 136) = 126/17
--   is a consequence of these forced ratios.

-- Dimension-coefficient products (verified by refl):
dim-Hermitian : ℕ
dim-Hermitian = 136

dim-NonHermitian : ℕ
dim-NonHermitian = 112

-- δ = 126/17 verification chain:
check-δ : 126 · 680 ≡ 17 · 5040
check-δ = refl


-- ================================================================
-- §D. Summary: Progress Report
-- ================================================================
--
-- ┌──────────────────────────────────────────────────────────────┐
-- │  PART A: Zero Simplification — ALL PROVED (no postulates)    │
-- ├──────────────────────────────────────────────────────────────┤
-- │  ✅ P-of-bracket-PQ : P[pureP p, pureQ q]₈ ≡ 0            │
-- │  ✅ Q-of-bracket-PQ : Q[pureP p, pureQ q]₈ ≡ 0            │
-- │  ✅ P-of-bracket-QP : P[pureQ q, pureP p]₈ ≡ 0            │
-- │  ✅ Q-of-bracket-QP : Q[pureQ q, pureP p]₈ ≡ 0            │
-- │  ✅ P-of-bracket-PP : P[pureP p₁, pureP p₂]₈ ≡ 0          │
-- │  ✅ Q-of-bracket-PP : Q[pureP p₁, pureP p₂]₈ ≡ 0          │
-- ├──────────────────────────────────────────────────────────────┤
-- │  PART B: P-component of outer brackets — ANALYZED            │
-- ├──────────────────────────────────────────────────────────────┤
-- │  📊 P-outer-1 = -E7-act(p₂×Fp₃)(p₁) - ⟨p₂,p₃⟩⊛p₁       │
-- │  📊 The cyclic sum involves ×F-derivation                   │
-- │  📝 Full proof deferred (next implementation phase)          │
-- ├──────────────────────────────────────────────────────────────┤
-- │  PART C: r-component and δ = 126/17 — ANALYZED              │
-- ├──────────────────────────────────────────────────────────────┤
-- │  ✅ r-of-bracket-QP : r[pureQ q, pureP p]₈ ≡ -⟨p,q⟩ₛ     │
-- │  ✅ r-of-bracket-PP : r[pureP p₁, pureP p₂]₈ ≡ 0          │
-- │  📊 δ enters via AdInvariance of B₈, not pure Jacobi       │
-- │  ✅ check-δ : 126·680 ≡ 17·5040 (refl)                     │
-- └──────────────────────────────────────────────────────────────┘
--
-- KEY DISCOVERY:
--   For pure distortion elements, the P-component of the
--   outer bracket reduces to exactly TWO non-zero terms:
--     (a) E7-act(p₂ ×F p₃)(p₁)  — Freudenthal cross → adjoint
--     (b) ⟨p₂,p₃⟩ₛ ⊛P p₁       — symplectic → scalar coupling
--
--   Term (a) is where ×F-derivation acts as the "magic wand"
--   to absorb non-associativity.
--   Term (b) is where the symplectic structure (and ultimately
--   the Killing form coefficients) regulate the "energy flow"
--   between distortion and core.
--
-- NEXT STEPS:
--   [ ] Compute all three P-outer terms explicitly
--   [ ] Form the cyclic sum
--   [ ] Apply ×F-derivation to show cancellation
--   [ ] Formalize AdInvariance → CoefficientForcing
