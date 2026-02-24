{-# OPTIONS --cubical --safe --guardedness -WnoUnsupportedIndexedMatch #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.BigOps using (module Sum; module KroneckerDelta)
open import Cubical.Data.Nat using (ℕ; zero; suc; _∸_)
open import Cubical.Data.FinData using (Fin; toℕ; fromℕ; toFromId; zero; suc) 

-- 🌌 UMIN エンジンと「完成した3つの床」をインポート
module UMIN.L00_Core.Instance.FPS_MonoidalCat {ℓ} (R : Ring ℓ) where

open import UMIN.L00_Core.Logic.EquationEngine
open import UMIN.L00_Core.Logic.FPS_Assoc R
open import UMIN.L00_Core.Algebra.FPS_Base R

open RingStr (snd R) renaming
  ( _+_  to _+R_
  ; _·_  to _*R_
  ; 0r   to 0R
  ; 1r   to 1R )

private
  Carrier : Type ℓ
  Carrier = fst R

-- =======================================================================
-- 2. テンソル積と単位元の定義
-- =======================================================================
unit-FPS : FPS-Obj
unit-FPS zero = 1R
unit-FPS (suc n) = 0R

-- =======================================================================
-- 3. 構造射（アソシエータと単位律）
-- =======================================================================

FPS-α : (A B C : FPS-Obj) → (A ⊗ B) ⊗ C ≡ A ⊗ (B ⊗ C)
FPS-α A B C = FPS-α-proof A B C

open Sum R
open KroneckerDelta R

unit-FPS-δ : (n : ℕ) (k : Fin (suc n)) → unit-FPS (toℕ k) ≡ δ {n = suc n} zero k
unit-FPS-δ n zero = refl
unit-FPS-δ n (suc k) = refl

lemma-λ-shift : ∀ (A : FPS-Obj) (n : ℕ) →
  (unit-FPS ⊗ A) (suc n) ≡ A (suc n)
lemma-λ-shift A n =
  (unit-FPS ⊗ A) (suc n)
    ≡⟨ refl ⟩
  ∑ {n = suc (suc n)} (λ k → unit-FPS (toℕ k) *R A (suc n ∸ toℕ k))
    ≡⟨ ∑Ext {n = suc (suc n)} (λ k → cong (_*R A (suc n ∸ toℕ k)) (unit-FPS-δ (suc n) k)) ⟩
  ∑ {n = suc (suc n)} (λ k → δ {n = suc (suc n)} zero k *R A (suc n ∸ toℕ k))
    ≡⟨ ∑Mul1r (suc (suc n)) (λ k → A (suc n ∸ toℕ k)) zero ⟩
  A (suc n ∸ toℕ (zero {n = suc n}))
    ≡⟨ refl ⟩
  A (suc n) ∎

unit-FPS⊗A-zero : (A : FPS-Obj) → (unit-FPS ⊗ A) zero ≡ 1R *R A zero
unit-FPS⊗A-zero A =
  ∑Last {n = 0} (λ k → unit-FPS (toℕ k) *R A (0 ∸ toℕ k)) ∙ +IdL (1R *R A zero)

proof-λ : (A : FPS-Obj) (n : ℕ) → (unit-FPS ⊗ A) n ≡ A n
proof-λ A zero =
  (unit-FPS ⊗ A) zero
    ≡⟨ unit-FPS⊗A-zero A ⟩
  1R *R A zero
    ≡⟨ ·IdL (A zero) ⟩
  A zero ∎
proof-λ A (suc n) = lemma-λ-shift A n

FPS-λ : (A : FPS-Obj) → unit-FPS ⊗ A ≡ A
FPS-λ A = fps-ext (proof-λ A)

unit-FPS-δ-ρ : (n : ℕ) (k : Fin (suc (suc n))) →
  unit-FPS (suc n ∸ toℕ k) ≡ δ {n = suc (suc n)} k (fromℕ (suc n))
unit-FPS-δ-ρ n zero = refl
unit-FPS-δ-ρ zero (suc zero) = refl
unit-FPS-δ-ρ (suc n) (suc j) = unit-FPS-δ-ρ n j

lemma-ρ-shift : ∀ (A : FPS-Obj) (n : ℕ) →
  (A ⊗ unit-FPS) (suc n) ≡ A (suc n)
lemma-ρ-shift A n =
  (A ⊗ unit-FPS) (suc n)
    ≡⟨ refl ⟩
  ∑ {n = suc (suc n)} (λ k → A (toℕ k) *R unit-FPS (suc n ∸ toℕ k))
    ≡⟨ ∑Ext {n = suc (suc n)} (λ k → cong (A (toℕ k) *R_) (unit-FPS-δ-ρ n k)) ⟩
  ∑ {n = suc (suc n)} (λ k → A (toℕ k) *R δ {n = suc (suc n)} k (fromℕ (suc n)))
    ≡⟨ ∑Mulr1 (suc (suc n)) (λ k → A (toℕ k)) (fromℕ (suc n)) ⟩
  A (toℕ (fromℕ (suc n)))
    ≡⟨ cong A (toFromId (suc n)) ⟩
  A (suc n) ∎

A⊗unit-FPS-zero : (A : FPS-Obj) → (A ⊗ unit-FPS) zero ≡ A zero *R 1R
A⊗unit-FPS-zero A =
  ∑Last {n = 0} (λ k → A (toℕ k) *R unit-FPS (0 ∸ toℕ k)) ∙ +IdL (A zero *R 1R)

proof-ρ : (A : FPS-Obj) (n : ℕ) → (A ⊗ unit-FPS) n ≡ A n
proof-ρ A zero =
  (A ⊗ unit-FPS) zero
    ≡⟨ A⊗unit-FPS-zero A ⟩
  A zero *R 1R
    ≡⟨ ·IdR (A zero) ⟩
  A zero ∎
proof-ρ A (suc n) = lemma-ρ-shift A n

FPS-ρ : (A : FPS-Obj) → A ⊗ unit-FPS ≡ A
FPS-ρ A = fps-ext (proof-ρ A)

-- =======================================================================
-- 4. コヒーレンス条件（ホモトピー型理論の魔法）
-- =======================================================================

FPS-isSet : isSet FPS-Obj
FPS-isSet = isSetΠ (λ _ → RingStr.is-set (snd R))

FPS-pentagon : (A B C D : FPS-Obj) →
  (cong (_⊗ D) (FPS-α A B C) ∙ FPS-α A (B ⊗ C) D ∙ cong (A ⊗_) (FPS-α B C D))
    ≡ (FPS-α (A ⊗ B) C D ∙ FPS-α A B (C ⊗ D))
FPS-pentagon A B C D = FPS-isSet _ _ _ _

FPS-triangle : (A B : FPS-Obj) →
  cong (_⊗ B) (FPS-ρ A) ≡ FPS-α A unit-FPS B ∙ cong (A ⊗_) (FPS-λ B)
FPS-triangle A B = FPS-isSet _ _ _ _

-- =======================================================================
-- 5. 🚀 最終定理：形式冪級数は弱モノイダル圏をなす
-- =======================================================================

record WeakMonoidalCategory : Type (ℓ-suc ℓ) where
  field
    Obj    : Type ℓ
    tensor : Obj → Obj → Obj
    unit   : Obj
    α      : (A B C : Obj) → tensor (tensor A B) C ≡ tensor A (tensor B C)
    leftUnitor  : (A : Obj) → tensor unit A ≡ A
    rightUnitor : (A : Obj) → tensor A unit ≡ A
    pentagon : (A B C D : Obj) →
      (cong (λ x → tensor x D) (α A B C) ∙ α A (tensor B C) D ∙ cong (tensor A) (α B C D))
      ≡ (α (tensor A B) C D ∙ α A B (tensor C D))
    triangle : (A B : Obj) →
      cong (λ x → tensor x B) (rightUnitor A) ≡ α A unit B ∙ cong (tensor A) (leftUnitor B)

FPS-MonoidalCat : WeakMonoidalCategory
FPS-MonoidalCat = record
  { Obj         = FPS-Obj
  ; tensor      = _⊗_
  ; unit        = unit-FPS
  ; α           = FPS-α
  ; leftUnitor  = FPS-λ
  ; rightUnitor = FPS-ρ
  ; pentagon    = FPS-pentagon
  ; triangle    = FPS-triangle
  }