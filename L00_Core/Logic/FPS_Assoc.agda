{-# OPTIONS --cubical --safe --guardedness #-}

open import Cubical.Algebra.Ring

module UMIN.L00_Core.Logic.FPS_Assoc {ℓ} (R : Ring ℓ) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ; zero; suc; _∸_) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Properties using (+-comm; +-suc; injSuc; snotz)
open import Cubical.Data.Empty using (⊥; elim) renaming (rec to ⊥-elim)
open import Cubical.Data.Nat.Order using (_≤_; zero-≤; ≤-refl)
open import UMIN.L00_Core.Logic.EquationEngine
open import UMIN.L00_Core.Algebra.FPS_Base R

-- ======================================================================
-- 1. 標準ライブラリ Ring と過去資産のブリッジ
-- ======================================================================
private
  Carrier : Type ℓ
  Carrier = fst R

open RingStr (snd R) renaming
  ( _+_  to _+R_
  ; _·_  to _*R_
  ; 0r   to 0R
  ; 1r   to 1R
  ; +Assoc  to +R-assoc-std
  ; +Comm   to +R-comm
  ; ·Assoc  to *R-assoc-std
  ; ·DistR+ to R-distribʳ
  ; ·DistL+ to R-distribˡ
  )

+R-assoc : ∀ x y z → (x +R y) +R z ≡ x +R (y +R z)
+R-assoc x y z = sym (+R-assoc-std x y z)

*R-assoc : ∀ x y z → (x *R y) *R z ≡ x *R (y *R z)
*R-assoc x y z = sym (*R-assoc-std x y z)

finiteSum : (ℕ → Carrier) → ℕ → Carrier
finiteSum f zero = f zero
finiteSum f (suc n) = finiteSum f n +R f (suc n)

-- ======================================================================
-- 2. 補題群 & ラスボス討伐
-- ======================================================================
abstract
  sum-plus-sum : ∀ n (f g : ℕ → Carrier) → 
    finiteSum (λ k → f k +R g k) n ≡ finiteSum f n +R finiteSum g n
  sum-plus-sum zero f g = refl
  sum-plus-sum (suc n) f g = 
    finiteSum (λ k → f k +R g k) n +R (f (suc n) +R g (suc n))
    ≡⟨ cong (λ x → x +R (f (suc n) +R g (suc n))) (sum-plus-sum n f g) ⟩⇒
      (finiteSum f n +R finiteSum g n) +R (f (suc n) +R g (suc n))
    ≡⟨ +R-assoc (finiteSum f n) (finiteSum g n) (f (suc n) +R g (suc n)) ⟩⇒
      finiteSum f n +R (finiteSum g n +R (f (suc n) +R g (suc n)))
    ≡⟨ cong (λ x → finiteSum f n +R x) (sym (+R-assoc (finiteSum g n) (f (suc n)) (g (suc n)))) ⟩⇒
      finiteSum f n +R ((finiteSum g n +R f (suc n)) +R g (suc n))
    ≡⟨ cong (λ x → finiteSum f n +R (x +R g (suc n))) (+R-comm (finiteSum g n) (f (suc n))) ⟩⇒
      finiteSum f n +R ((f (suc n) +R finiteSum g n) +R g (suc n))
    ≡⟨ cong (λ x → finiteSum f n +R x) (+R-assoc (f (suc n)) (finiteSum g n) (g (suc n))) ⟩⇒
      finiteSum f n +R (f (suc n) +R (finiteSum g n +R g (suc n)))
    ≡⟨ sym (+R-assoc (finiteSum f n) (f (suc n)) (finiteSum g n +R g (suc n))) ⟩⇒
      (finiteSum f n +R f (suc n)) +R (finiteSum g n +R g (suc n))
    ∎⇒

  finiteSum-ext : ∀ n (f g : ℕ → Carrier) → (∀ k → k ≤ n → f k ≡ g k) → finiteSum f n ≡ finiteSum g n
  finiteSum-ext zero f g hyp = hyp zero zero-≤
  finiteSum-ext (suc n) f g hyp = 
    cong₂ _+R_ (finiteSum-ext n f g (λ k k≤n → hyp k (suc-≤ k≤n))) 
               (hyp (suc n) ≤-refl)
    where
      suc-≤ : ∀ {m n} → m ≤ n → m ≤ suc n
      suc-≤ (k , p) = (suc k) , (cong suc p)

  j≤0→j≡0 : ∀ j → j ≤ 0 → j ≡ 0
  j≤0→j≡0 zero _ = refl
  j≤0→j≡0 (suc j) (k , p) = ⊥-elim (snotz (sym (+-comm k (suc j)) ∙ p))

  +-∸-assoc-lemma : ∀ i j → j ≤ i → j +ℕ (i ∸ j) ≡ i
  +-∸-assoc-lemma zero j j≤0 = cong (λ x → x +ℕ (0 ∸ x)) (j≤0→j≡0 j j≤0)
  +-∸-assoc-lemma (suc i) zero _ = refl
  +-∸-assoc-lemma (suc i) (suc j) (k , p) = cong suc (+-∸-assoc-lemma i j (k , lemma))
    where
      lemma : k +ℕ j ≡ i
      lemma = injSuc (sym (+-suc k j) ∙ p)

  zero∸ : ∀ m → 0 ∸ m ≡ 0
  zero∸ zero = refl
  zero∸ (suc m) = refl

  ∸-dist-lemma : ∀ n k m → n ∸ (k +ℕ m) ≡ (n ∸ k) ∸ m
  ∸-dist-lemma n zero m = refl
  ∸-dist-lemma zero (suc k) m = sym (zero∸ m)
  ∸-dist-lemma (suc n) (suc k) m = ∸-dist-lemma n k m
  
  suc-∸-lemma : ∀ n k → k ≤ n → suc n ∸ k ≡ suc (n ∸ k)
  suc-∸-lemma n zero _ = refl
  suc-∸-lemma (suc n) (suc k) (x , p) = suc-∸-lemma n k (x , lemma-p)
    where
      lemma-p : x +ℕ k ≡ n
      lemma-p = injSuc (sym (+-suc x k) ∙ p)
  suc-∸-lemma zero (suc k) (x , p) = ⊥-elim (snotz (sym (+-suc x k) ∙ p))

  n∸n≡0 : ∀ n → n ∸ n ≡ 0
  n∸n≡0 zero = refl
  n∸n≡0 (suc n) = n∸n≡0 n

  sum-distribʳ-lemma : ∀ n (c : Carrier) (f : ℕ → Carrier) → (finiteSum f n) *R c ≡ finiteSum (λ k → f k *R c) n
  sum-distribʳ-lemma zero c f = refl
  sum-distribʳ-lemma (suc n) c f =
    R-distribˡ (finiteSum f n) (f (suc n)) c
    ∙ cong (λ x → x +R (f (suc n) *R c)) (sum-distribʳ-lemma n c f)

  sum-distribˡ-lemma : ∀ n (c : Carrier) (f : ℕ → Carrier) → c *R (finiteSum f n) ≡ finiteSum (λ k → c *R f k) n
  sum-distribˡ-lemma zero c f = refl
  sum-distribˡ-lemma (suc n) c f =
    R-distribʳ c (finiteSum f n) (f (suc n))
    ∙ cong (λ x → x +R (c *R f (suc n))) (sum-distribˡ-lemma n c f)

  double-sum-swap-lemma : (n : ℕ) (F : ℕ → ℕ → Carrier) → 
    finiteSum (λ i → finiteSum (λ j → F j (i ∸ j)) i) n 
    ≡ finiteSum (λ k → finiteSum (λ m → F k m) (n ∸ k)) n
  double-sum-swap-lemma zero F = refl
  double-sum-swap-lemma (suc n) F = 
    finiteSum (λ i → finiteSum (λ j → F j (i ∸ j)) i) n 
    +R finiteSum (λ j → F j (suc n ∸ j)) (suc n)
    ≡⟨ cong (λ x → x +R finiteSum (λ j → F j (suc n ∸ j)) (suc n)) (double-sum-swap-lemma n F) ⟩⇒
      finiteSum (λ k → finiteSum (λ m → F k m) (n ∸ k)) n 
      +R finiteSum (λ j → F j (suc n ∸ j)) (suc n)
    ≡⟨ refl ⟩⇒
      finiteSum (λ k → finiteSum (λ m → F k m) (n ∸ k)) n 
      +R (finiteSum (λ j → F j (suc n ∸ j)) n +R F (suc n) (suc n ∸ suc n))
    ≡⟨ cong (λ x → finiteSum (λ k → finiteSum (λ m → F k m) (n ∸ k)) n 
                     +R (finiteSum (λ j → F j (suc n ∸ j)) n +R F (suc n) x)) 
             (n∸n≡0 (suc n)) ⟩⇒
      finiteSum (λ k → finiteSum (λ m → F k m) (n ∸ k)) n 
      +R (finiteSum (λ j → F j (suc n ∸ j)) n +R F (suc n) 0)
    ≡⟨ sym (+R-assoc (finiteSum (λ k → finiteSum (λ m → F k m) (n ∸ k)) n) 
                      (finiteSum (λ j → F j (suc n ∸ j)) n) 
                      (F (suc n) 0)) ⟩⇒
      (finiteSum (λ k → finiteSum (λ m → F k m) (n ∸ k)) n 
       +R finiteSum (λ j → F j (suc n ∸ j)) n) 
      +R F (suc n) 0
    -- 💡 ここで _ _ を完全に関数化
    ≡⟨ cong (λ x → x +R F (suc n) 0) (sym (sum-plus-sum n 
         (λ k → finiteSum (λ m → F k m) (n ∸ k)) 
         (λ k → F k (suc n ∸ k)))) ⟩⇒
      finiteSum (λ k → finiteSum (λ m → F k m) (n ∸ k) +R F k (suc n ∸ k)) n 
      +R F (suc n) 0
    -- 💡 ここも _ _ を完全に関数化
    ≡⟨ cong (λ x → x +R F (suc n) 0) (finiteSum-ext n 
         (λ k → finiteSum (λ m → F k m) (n ∸ k) +R F k (suc n ∸ k)) 
         (λ k → finiteSum (λ m → F k m) (n ∸ k) +R F k (suc (n ∸ k))) 
         (λ k k≤n → cong₂ _+R_ refl (cong (F k) (suc-∸-lemma n k k≤n)))) ⟩⇒
      finiteSum (λ k → finiteSum (λ m → F k m) (n ∸ k) +R F k (suc (n ∸ k))) n 
      +R F (suc n) 0
    ≡⟨ refl ⟩⇒
       finiteSum (λ k → finiteSum (λ m → F k m) (suc (n ∸ k))) n 
       +R F (suc n) 0
    -- 💡 ここも _ _ を完全に関数化
    ≡⟨ cong (λ x → x +R F (suc n) 0) (finiteSum-ext n 
         (λ k → finiteSum (λ m → F k m) (suc (n ∸ k))) 
         (λ k → finiteSum (λ m → F k m) (suc n ∸ k)) 
         (λ k k≤n → cong (finiteSum (λ m → F k m)) (sym (suc-∸-lemma n k k≤n)))) ⟩⇒
       finiteSum (λ k → finiteSum (λ m → F k m) (suc n ∸ k)) n 
       +R F (suc n) 0
    ≡⟨ cong (λ x → finiteSum (λ k → finiteSum (λ m → F k m) (suc n ∸ k)) n +R x) 
             (sym (cong (finiteSum (λ m → F (suc n) m)) (n∸n≡0 n))) ⟩⇒
       finiteSum (λ k → finiteSum (λ m → F k m) (suc n ∸ k)) n 
       +R finiteSum (λ m → F (suc n) m) (n ∸ n)
    ≡⟨ refl ⟩⇒
       finiteSum (λ k → finiteSum (λ m → F k m) (suc n ∸ k)) (suc n)
    ∎⇒

-- ======================================================================
-- 3. 💥 最終定理：アソシエータ Φ のメインパス
-- ======================================================================
FPS-Obj : Type ℓ
FPS-Obj = FormalPowerSeries

open import Cubical.Algebra.Ring.BigOps using (module Sum)
open import Cubical.Data.FinData.Base
  using (Fin; toℕ; weakenFin; fromℕ; toFromId)
  renaming (zero to fzero; suc to fsuc)

open Sum R

distribRHS : FPS-Obj → FPS-Obj → FPS-Obj → FPS-Obj
distribRHS A B C n =
  finiteSum (λ i →
    finiteSum (λ j → (A j *R B (i ∸ j)) *R C (n ∸ i)) i) n

midRHS : FPS-Obj → FPS-Obj → FPS-Obj → FPS-Obj
midRHS A B C n =
  finiteSum (λ i →
    finiteSum (λ j → A j *R (B (i ∸ j) *R C (n ∸ i))) i) n

abstract
  -- 💡 完全に型を明示した toℕ-weakenFin
  toℕ-weakenFin : ∀ {n} (k : Fin n) → toℕ (weakenFin k) ≡ toℕ k
  toℕ-weakenFin {n} k = Cubical.Data.FinData.Base.elim
    (λ {m} (fn : Fin m) → toℕ (weakenFin fn) ≡ toℕ fn)
    refl
    (λ {m} {fn : Fin m} eq → cong suc eq)
    k

  sum-bridge : ∀ n (f : ℕ → Carrier) → 
    ∑ {n = suc n} (λ k → f (toℕ k)) ≡ finiteSum f n
  sum-bridge zero f =
    ∑Last {n = 0} (λ k → f (toℕ k))
    ∙ +IdL (f zero)
  sum-bridge (suc n) f =
    let
      V : Fin (suc (suc n)) → Carrier
      V k = f (toℕ k)
      p₁ : ∑ V ≡ ∑ (V ∘ weakenFin) +R V (fromℕ (suc n))
      p₁ = ∑Last {n = suc n} V
      pTailAlign : ∑ (V ∘ weakenFin) ≡ ∑ {n = suc n} (λ k → f (toℕ k))
      pTailAlign = ∑Ext {n = suc n} (λ k → cong f (toℕ-weakenFin k))
      p₂ : ∑ (V ∘ weakenFin) ≡ finiteSum f n
      p₂ = pTailAlign ∙ sum-bridge n f
      step : ∑ (V ∘ weakenFin) +R V (fromℕ (suc n)) ≡ ∑ (V ∘ weakenFin) +R f (suc n)
      step = cong (∑ (V ∘ weakenFin) +R_) (cong f (toFromId (suc n)))
      p₃ : ∑ (V ∘ weakenFin) +R f (suc n) ≡ finiteSum f n +R f (suc n)
      p₃ = cong (λ x → x +R f (suc n)) p₂
    in
      p₁ ∙ step ∙ p₃

  ⊗-finiteSum : ∀ (A B : FPS-Obj) n →
    (A ⊗ B) n ≡ finiteSum (λ k → A k *R B (n ∸ k)) n
  ⊗-finiteSum A B n = sum-bridge n (λ k → A k *R B (n ∸ k))

  assoc-distrib : ∀ (A B C : FPS-Obj) →
    ((A ⊗ B) ⊗ C) ≡ distribRHS A B C
  assoc-distrib A B C = fps-ext λ n →
    ((A ⊗ B) ⊗ C) n
    ≡⟨ ⊗-finiteSum (A ⊗ B) C n ⟩⇒
      finiteSum (λ i → (A ⊗ B) i *R C (n ∸ i)) n
    ≡⟨ cong (λ F → finiteSum F n) (funExt λ i → 
         cong (λ X → X *R C (n ∸ i)) (⊗-finiteSum A B i)) ⟩⇒
      finiteSum (λ i → finiteSum (λ j → A j *R B (i ∸ j)) i *R C (n ∸ i)) n
    ≡⟨ cong (λ F → finiteSum F n) (funExt λ i → 
         sum-distribʳ-lemma i (C (n ∸ i)) (λ j → A j *R B (i ∸ j))) ⟩⇒
      distribRHS A B C n ∎⇒

  assoc-proof : ∀ (A B C : FPS-Obj) →
    distribRHS A B C ≡ midRHS A B C
  assoc-proof A B C = fps-ext λ n →
    cong (λ (F : ℕ → Carrier) → finiteSum F n)
         (funExt λ (i : ℕ) →
           cong (λ (G : ℕ → Carrier) → finiteSum G i)
                (funExt λ (j : ℕ) →
                  *R-assoc (A j) (B (i ∸ j)) (C (n ∸ i))))

  assoc-block3 : ∀ (A B C : FPS-Obj) →
    midRHS A B C ≡ (A ⊗ (B ⊗ C))
  assoc-block3 A B C = fps-ext λ n →
    midRHS A B C n
    -- 💡 ここも _ _ を完全に関数化
    ≡⟨ cong (λ F → finiteSum F n) (funExt λ i →
         finiteSum-ext i 
           (λ j → A j *R (B (i ∸ j) *R C (n ∸ i))) 
           (λ j → A j *R (B (i ∸ j) *R C (n ∸ (j +ℕ (i ∸ j))))) 
           (λ j j≤i → cong (λ X → A j *R (B (i ∸ j) *R C (n ∸ X)))
                (sym (+-∸-assoc-lemma i j j≤i)))) ⟩⇒
      finiteSum (λ i → finiteSum (λ j → A j *R (B (i ∸ j) *R C (n ∸ (j +ℕ (i ∸ j))))) i) n
    ≡⟨ double-sum-swap-lemma n (λ k m → A k *R (B m *R C (n ∸ (k +ℕ m)))) ⟩⇒
      finiteSum (λ k → finiteSum (λ m → A k *R (B m *R C (n ∸ (k +ℕ m)))) (n ∸ k)) n
    ≡⟨ cong (λ F → finiteSum F n) (funExt λ k →
         sym (sum-distribˡ-lemma (n ∸ k) (A k) (λ m → B m *R C (n ∸ (k +ℕ m))))) ⟩⇒
      finiteSum (λ k → A k *R finiteSum (λ m → B m *R C (n ∸ (k +ℕ m))) (n ∸ k)) n
    ≡⟨ cong (λ F → finiteSum F n) (funExt λ k →
         cong (λ X → A k *R X)
         (cong (λ G → finiteSum G (n ∸ k)) (funExt λ m →
           cong (λ Y → B m *R C Y) (∸-dist-lemma n k m)))) ⟩⇒
      finiteSum (λ k → A k *R finiteSum (λ m → B m *R C ((n ∸ k) ∸ m)) (n ∸ k)) n
    ≡⟨ cong (λ F → finiteSum F n) (funExt λ k → 
         cong (λ X → A k *R X) (sym (⊗-finiteSum B C (n ∸ k)))) ⟩⇒
      finiteSum (λ k → A k *R (B ⊗ C) (n ∸ k)) n
    ≡⟨ sym (⊗-finiteSum A (B ⊗ C) n) ⟩⇒
      (A ⊗ (B ⊗ C)) n ∎⇒

  FPS-α-proof : ∀ (A B C : FPS-Obj) → 
    ((A ⊗ B) ⊗ C) ≡ (A ⊗ (B ⊗ C))
  FPS-α-proof A B C =
    assoc-distrib A B C ∙ assoc-proof A B C ∙ assoc-block3 A B C