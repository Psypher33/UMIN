{-# OPTIONS --cubical --guardedness --lossy-unification #-}

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.BigOps using (module Sum; module KroneckerDelta)
open import Cubical.Data.Nat using (ℕ; zero; suc; _∸_)
open import Cubical.Data.FinData using (Fin; toℕ; fromℕ; toFromId; zero; suc) 

-- 🌌 UMIN エンジンと「完成した3つの床」をインポート
module UMIN.L00_Core.Instance.FPS_MonoidalCat {ℓ} (R : Ring ℓ) where

open import UMIN.L00_Core.Logic.EquationEngine
open import UMIN.L00_Core.Logic.Pentagon_Coherence R
open import UMIN.L00_Core.Logic.FPS_Assoc R
  -- FPS_Base は Pentagon_Coherence が public で再エクスポートしているため、
  -- ここでは FPS_Base を直接 import しない（FormalPowerSeries 等の曖昧さを避ける）

-- Ring の構成要素を展開（このモジュール内での略記を導入）
open RingStr (snd R) renaming
  ( _+_  to _+R_
  ; _·_  to _*R_
  ; 0r   to 0R
  ; 1r   to 1R )

private
  Carrier : Type ℓ
  Carrier = fst R

-- =======================================================================
-- 1. モノイダル圏の要件（仮置・もしくは既存の定義をインポート）
-- =======================================================================
-- ※ WeakMonoidalCategory の定義は最終段階でインポートします。

-- =======================================================================
-- 2. テンソル積と単位元の定義
-- =======================================================================

-- 🌌 テンソル積（Cauchy Convolution）は FPS_Base の _⊗_ をそのまま使用

-- 🌌 単位元（モノイダル単位）
-- 0番目の成分が 1R、それ以外が 0R となる級数
unit-FPS : FPS-Obj
unit-FPS zero = 1R
unit-FPS (suc n) = 0R

-- =======================================================================
-- 3. 構造射（アソシエータと単位律）
-- =======================================================================

-- アソシエータ（Cauchy 積の結合律）
FPS-α : (A B C : FPS-Obj) → (A ⊗ B) ⊗ C ≡ A ⊗ (B ⊗ C)
FPS-α A B C = FPS-α-proof A B C

-- -----------------------------------------------------------------------
-- 🛡️ 左単位律（unit-FPS ⊗ A ≡ A）
-- -----------------------------------------------------------------------
open Sum R
open KroneckerDelta R

-- unit-FPS (toℕ k) は k=0 のとき 1R、それ以外 0R → δ zero k と一致
-- (n はパターンマッチせず、Fin のみで分岐して Cubical の警告を避ける)
unit-FPS-δ : (n : ℕ) (k : Fin (suc n)) → unit-FPS (toℕ k) ≡ δ zero k
unit-FPS-δ n zero = refl
unit-FPS-δ n (suc k) = refl

lemma-λ-shift : ∀ (A : FPS-Obj) (n : ℕ) →
  (unit-FPS ⊗ A) (suc n) ≡ A (suc n)
lemma-λ-shift A n =
  (unit-FPS ⊗ A) (suc n)
    ≡⟨ refl ⟩
  ∑ (λ k → unit-FPS (toℕ k) *R A (suc n ∸ toℕ k))
    ≡⟨ ∑Ext (λ k → cong (_*R A (suc n ∸ toℕ k)) (unit-FPS-δ (suc n) k)) ⟩
  ∑ (λ k → δ zero k *R A (suc n ∸ toℕ k))
    ≡⟨ ∑Mul1r (suc (suc n)) (λ k → A (suc n ∸ toℕ k)) zero ⟩
  A (suc n ∸ toℕ zero)
    ≡⟨ refl ⟩
  A (suc n) ∎

-- (unit-FPS ⊗ A) zero は Fin 1 の和なので ∑Last で先頭項に等しい
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

-- -----------------------------------------------------------------------
-- 🛡️ 右単位律（A ⊗ unit-FPS ≡ A）
-- -----------------------------------------------------------------------
-- unit-FPS (suc n ∸ toℕ k) は k = fromℕ (suc n) のときだけ 1R → δ k (fromℕ (suc n)) と一致
unit-FPS-δ-ρ : (n : ℕ) (k : Fin (suc (suc n))) →
  unit-FPS (suc n ∸ toℕ k) ≡ δ k (fromℕ (suc n))
unit-FPS-δ-ρ n zero = refl
unit-FPS-δ-ρ zero (suc zero) = refl
unit-FPS-δ-ρ (suc n) (suc j) = unit-FPS-δ-ρ n j

lemma-ρ-shift : ∀ (A : FPS-Obj) (n : ℕ) →
  (A ⊗ unit-FPS) (suc n) ≡ A (suc n)
lemma-ρ-shift A n =
  (A ⊗ unit-FPS) (suc n)
    ≡⟨ refl ⟩
  ∑ (λ k → A (toℕ k) *R unit-FPS (suc n ∸ toℕ k))
    ≡⟨ ∑Ext (λ k → cong (A (toℕ k) *R_) (unit-FPS-δ-ρ n k)) ⟩
  ∑ (λ k → A (toℕ k) *R δ k (fromℕ (suc n)))
    ≡⟨ ∑Mulr1 (suc (suc n)) (λ k → A (toℕ k)) (fromℕ (suc n)) ⟩
  A (toℕ (fromℕ (suc n)))
    ≡⟨ cong A (toFromId (suc n)) ⟩
  A (suc n) ∎

-- (A ⊗ unit-FPS) zero は Fin 1 の和なので ∑Last で先頭項に等しい
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
-- 4. コヒーレンス条件の組み込み（Pentagon Coherenceの呼び出し）
-- =======================================================================

postulate
  -- 五角形図式（Pentagon Identity）
  FPS-pentagon : (A B C D : FPS-Obj) →
    (cong (_⊗ D) (FPS-α A B C) ∙ FPS-α A (B ⊗ C) D ∙ cong (A ⊗_) (FPS-α B C D))
      ≡ (FPS-α (A ⊗ B) C D ∙ FPS-α A B (C ⊗ D))

  -- 三角形図式（Triangle Identity）
  FPS-triangle : (A B : FPS-Obj) →
    cong (_⊗ B) (FPS-ρ A) ≡ FPS-α A unit-FPS B ∙ cong (A ⊗_) (FPS-λ B)