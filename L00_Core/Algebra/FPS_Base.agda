{-# OPTIONS --cubical --safe --guardedness #-}

open import Cubical.Algebra.Ring

module UMIN.L00_Core.Algebra.FPS_Base {ℓ} (R : Ring ℓ) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws as GL
open import Cubical.Foundations.Path using (Square→compPath)
open import Cubical.Data.Nat using (ℕ; suc; _∸_)
open import Cubical.Data.FinData using (Fin; toℕ)

-- 🌌 UMIN エンジンのインポート
open import UMIN.L00_Core.Logic.EquationEngine
open import Cubical.Algebra.Ring.BigOps using (module Sum)

-- Ring の構成要素を展開（名前衝突を避けるためrenaming）
open RingStr (snd R) renaming
  ( _+_  to _+R_
  ; _·_  to _*R_
  ; 0r   to 0R
  ; 1r   to 1R
  ; -_   to negR )

private
  Carrier : Type ℓ
  Carrier = fst R

  open Sum R

-- =======================================================================
-- 1. 形式冪級数の基本定義
-- =======================================================================

FormalPowerSeries : Type ℓ
FormalPowerSeries = ℕ → Carrier

fps-ext : {A B : FormalPowerSeries}
        → (∀ n → A n ≡ B n) → A ≡ B
fps-ext = funExt

-- =======================================================================
-- 2. 基本演算（ここに ⊗ を追加しました）
-- =======================================================================

-- 加法（点ごと）
_⊞_ : FormalPowerSeries → FormalPowerSeries → FormalPowerSeries
(A ⊞ B) n = A n +R B n

-- スカラー倍
_⊙_ : Carrier → FormalPowerSeries → FormalPowerSeries
(r ⊙ A) n = r *R A n

-- 【新規追加】乗法（Cauchy積）(A ⊗ B)_n = Σ_{k=0}^{n} A_k · B_{n-k}
_⊗_ : FormalPowerSeries → FormalPowerSeries → FormalPowerSeries
(A ⊗ B) n = ∑ (λ (k : Fin (suc n)) → A (toℕ k) *R B (n ∸ toℕ k)) 

-- 演算子の優先順位を定義（⊗ を ⊞ より強く結びつくようにします）
infixl 7 _⊗_
infixl 6 _⊞_

-- =======================================================================
-- 3. パス演算（Interchange Laws の基盤）
-- =======================================================================

-- パスの成分ごとの積
_*P_ : {A A' B B' : Carrier}
     → A ≡ A' → B ≡ B' → A *R B ≡ A' *R B'
p *P q = cong₂ _*R_ p q

-- =======================================================================
-- 4. Eckmann-Hilton 交換律
-- =======================================================================
-- (p1 ∙ p2) *P (q1 ∙ q2) ≡ (p1 *P q1) ∙ (p2 *P q2)

private
  *R-square : ∀ (a b v w : Carrier) (p : a ≡ b) (s : v ≡ w) →
    (cong (a *R_) s) ∙ (cong (λ x → x *R w) p)
      ≡ (cong (λ x → x *R v) p) ∙ (cong (b *R_) s)
  *R-square a b v w p s =
    sym (Square→compPath (λ i j → p i *R s j))

*P-∙ : {A B C D E F : Carrier}
     → (p1 : A ≡ B) (p2 : B ≡ C)
     → (q1 : D ≡ E) (q2 : E ≡ F)
     → (p1 ∙ p2) *P (q1 ∙ q2) ≡ (p1 *P q1) ∙ (p2 *P q2)
*P-∙ {A} {B} {C} {D} {E} {F} p1 p2 q1 q2 =
  begin⇒_
    (p1 ∙ p2) *P (q1 ∙ q2)
  ≡⟨ GL.cong₂Funct _*R_ (p1 ∙ p2) (q1 ∙ q2) ⟩⇒
    (cong (λ x → x *R D) (p1 ∙ p2)) ∙ (cong (C *R_) (q1 ∙ q2))
  ≡⟨ (λ i → (GL.cong-∙ (λ x → x *R D) p1 p2 i)
             ∙ (GL.cong-∙ (C *R_) q1 q2 i)) ⟩⇒
    ((cong (λ x → x *R D) p1 ∙ cong (λ x → x *R D) p2)
      ∙ (cong (C *R_) q1 ∙ cong (C *R_) q2))
  ≡⟨ (GL.assoc (cong (λ x → x *R D) p1 ∙ cong (λ x → x *R D) p2)
                (cong (C *R_) q1)
                (cong (C *R_) q2))
     ∙ cong (_∙ cong (C *R_) q2)
            (sym (GL.assoc (cong (λ x → x *R D) p1)
                            (cong (λ x → x *R D) p2)
                            (cong (C *R_) q1))) ⟩⇒
    (cong (λ x → x *R D) p1 ∙ (cong (λ x → x *R D) p2 ∙ cong (C *R_) q1))
      ∙ cong (C *R_) q2
  ≡⟨ cong (λ φ → (cong (λ x → x *R D) p1 ∙ φ) ∙ cong (C *R_) q2)
           (sym (*R-square B C D E p2 q1)) ⟩⇒
    (cong (λ x → x *R D) p1 ∙ (cong (B *R_) q1 ∙ cong (λ x → x *R E) p2))
      ∙ cong (C *R_) q2
  ≡⟨ cong (_∙ cong (C *R_) q2)
           (GL.assoc (cong (λ x → x *R D) p1)
                     (cong (B *R_) q1)
                     (cong (λ x → x *R E) p2)) ⟩⇒
    ((cong (λ x → x *R D) p1 ∙ cong (B *R_) q1)
      ∙ cong (λ x → x *R E) p2) ∙ cong (C *R_) q2
  ≡⟨ sym (GL.assoc ((cong (λ x → x *R D) p1) ∙ (cong (B *R_) q1))
                    (cong (λ x → x *R E) p2)
                    (cong (C *R_) q2)) ⟩⇒
    (cong (λ x → x *R D) p1 ∙ cong (B *R_) q1)
      ∙ (cong (λ x → x *R E) p2 ∙ cong (C *R_) q2)
  ≡⟨ (λ i → (sym (GL.cong₂Funct _*R_ p1 q1) i)
             ∙ (sym (GL.cong₂Funct _*R_ p2 q2) i)) ⟩⇒
    (p1 *P q1) ∙ (p2 *P q2)
  ∎⇒