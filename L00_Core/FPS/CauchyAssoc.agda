{-# OPTIONS --cubical --safe --guardedness #-}

module UMIN.L00_Core.FPS.CauchyAssoc where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function hiding (_∘_)
open import Cubical.Data.Nat using (ℕ; _∸_; suc; zero; snotz) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Properties using (+-comm; +-suc; injSuc)
open import Cubical.Data.Empty using (⊥; elim) renaming (rec to ⊥-elim)
open import Cubical.Data.Nat.Order using (_≤_; zero-≤; ≤-refl)

-- begin の優先順位を下げてパースエラーを防ぐ
infix 1 begin_
begin_ : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ≡ y → x ≡ y
begin p = p

-- ======================================================================
-- 1. 基礎構造（Ring, 形式冪級数, Cauchy積）
-- ======================================================================
record Ring (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    Carrier : Type ℓ
    is-set  : isSet Carrier  -- 💡 【追加】この空間は穴のない「Set」であるという公理
    _+_ _*_ : Carrier → Carrier → Carrier
    0# 1# : Carrier
    +R-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
    +R-comm  : ∀ x y → x + y ≡ y + x
    *R-assoc : ∀ x y z → (x * y) * z ≡ x * (y * z)
    R-distribʳ : ∀ x y z → (x + y) * z ≡ (x * z) + (y * z)
    R-distribˡ : ∀ x y z → x * (y + z) ≡ (x * y) + (x * z)

FormalPowerSeries : ∀ {ℓ} → Ring ℓ → Type ℓ
FormalPowerSeries R = ℕ → Ring.Carrier R

finiteSum : ∀ {ℓ} (R : Ring ℓ) → (ℕ → Ring.Carrier R) → ℕ → Ring.Carrier R
finiteSum R f zero = f zero
finiteSum R f (suc n) = let open Ring R in finiteSum R f n + f (suc n)

cauchy : ∀ {ℓ} (R : Ring ℓ) → FormalPowerSeries R → FormalPowerSeries R → FormalPowerSeries R
cauchy R A B n = let open Ring R in finiteSum R (λ k → A k * B (n ∸ k)) n

-- ======================================================================
-- 2. 補題群 & ラスボス討伐
-- ======================================================================
module CauchyProofs {ℓ} (R : Ring ℓ) where
  open Ring R

  -- 補題: 和の分離 ∑(f + g) = ∑f + ∑g
  sum-plus-sum : ∀ n (f g : ℕ → Carrier) → 
    finiteSum R (λ k → f k + g k) n ≡ finiteSum R f n + finiteSum R g n
  sum-plus-sum zero f g = refl
  sum-plus-sum (suc n) f g = 
    begin
      finiteSum R (λ k → f k + g k) n + (f (suc n) + g (suc n))
    ≡⟨ cong (λ x → x + (f (suc n) + g (suc n))) (sum-plus-sum n f g) ⟩
      (finiteSum R f n + finiteSum R g n) + (f (suc n) + g (suc n))
    ≡⟨ +R-assoc (finiteSum R f n) (finiteSum R g n) (f (suc n) + g (suc n)) ⟩
      finiteSum R f n + (finiteSum R g n + (f (suc n) + g (suc n)))
    ≡⟨ cong (λ x → finiteSum R f n + x) (sym (+R-assoc (finiteSum R g n) (f (suc n)) (g (suc n)))) ⟩
      finiteSum R f n + ((finiteSum R g n + f (suc n)) + g (suc n))
    ≡⟨ cong (λ x → finiteSum R f n + (x + g (suc n))) (+R-comm (finiteSum R g n) (f (suc n))) ⟩
      finiteSum R f n + ((f (suc n) + finiteSum R g n) + g (suc n))
    ≡⟨ cong (λ x → finiteSum R f n + x) (+R-assoc (f (suc n)) (finiteSum R g n) (g (suc n))) ⟩
      finiteSum R f n + (f (suc n) + (finiteSum R g n + g (suc n)))
    ≡⟨ sym (+R-assoc (finiteSum R f n) (f (suc n)) (finiteSum R g n + g (suc n))) ⟩
      (finiteSum R f n + f (suc n)) + (finiteSum R g n + g (suc n))
    ∎

  -- 🗡️ 補題1: finiteSum-ext
  finiteSum-ext : ∀ n (f g : ℕ → Carrier) → (∀ k → k ≤ n → f k ≡ g k) → finiteSum R f n ≡ finiteSum R g n
  finiteSum-ext zero f g hyp = hyp zero zero-≤
  finiteSum-ext (suc n) f g hyp = 
    cong₂ _+_ (finiteSum-ext n f g (λ k k≤n → hyp k (suc-≤ k≤n))) 
              (hyp (suc n) ≤-refl)
    where
      suc-≤ : ∀ {m n} → m ≤ n → m ≤ suc n
      suc-≤ (k , p) = (suc k) , (cong suc p)

  -- 🗡️ 補題X: 0の周辺の型理論的証明
  j≤0→j≡0 : ∀ j → j ≤ 0 → j ≡ 0
  j≤0→j≡0 zero _ = refl
  j≤0→j≡0 (suc j) (k , p) = ⊥-elim (snotz (sym (+-comm k (suc j)) ∙ p))

  -- 🗡️ 補題3: インデックス調整 j + (i - j) ≡ i
  +-∸-assoc-lemma : ∀ i j → j ≤ i → j +ℕ (i ∸ j) ≡ i
  +-∸-assoc-lemma zero j j≤0 = cong (λ x → x +ℕ (0 ∸ x)) (j≤0→j≡0 j j≤0)
  +-∸-assoc-lemma (suc i) zero _ = refl
  +-∸-assoc-lemma (suc i) (suc j) (k , p) = cong suc (+-∸-assoc-lemma i j (k , lemma))
    where
      lemma : k +ℕ j ≡ i
      lemma = injSuc (sym (+-suc k j) ∙ p)

  -- 🗡️ 補題4: 引き算の分配
  zero∸ : ∀ m → 0 ∸ m ≡ 0
  zero∸ zero = refl
  zero∸ (suc m) = refl

  ∸-dist-lemma : ∀ n k m → n ∸ (k +ℕ m) ≡ (n ∸ k) ∸ m
  ∸-dist-lemma n zero m = refl
  ∸-dist-lemma zero (suc k) m = sym (zero∸ m)
  ∸-dist-lemma (suc n) (suc k) m = ∸-dist-lemma n k m
  
  -- 🗡️ 補題4.5: suc n ∸ k ≡ suc (n ∸ k)
  suc-∸-lemma : ∀ n k → k ≤ n → suc n ∸ k ≡ suc (n ∸ k)
  suc-∸-lemma n zero _ = refl
  suc-∸-lemma (suc n) (suc k) (x , p) = suc-∸-lemma n k (x , lemma-p)
    where
      lemma-p : x +ℕ k ≡ n
      lemma-p = injSuc (sym (+-suc x k) ∙ p)
  -- 【修正】CoverageIssueの解消: (suc k) ≤ 0 はあり得ないので矛盾で処理
  suc-∸-lemma zero (suc k) (x , p) = ⊥-elim (snotz (sym (+-suc x k) ∙ p))

  -- 🗡️ 補題4.6: n ∸ n ≡ 0 (double-sum-swap-lemmaの最後で必要)
  n∸n≡0 : ∀ n → n ∸ n ≡ 0
  n∸n≡0 zero = refl
  n∸n≡0 (suc n) = n∸n≡0 n

  -- 🗡️ 補題5: 右分配
  sum-distribʳ-lemma : ∀ n (c : Carrier) (f : ℕ → Carrier) → (finiteSum R f n) * c ≡ finiteSum R (λ k → f k * c) n
  sum-distribʳ-lemma zero c f = refl
  sum-distribʳ-lemma (suc n) c f =
    R-distribʳ (finiteSum R f n) (f (suc n)) c
    ∙ cong (λ x → x + (f (suc n) * c)) (sum-distribʳ-lemma n c f)

  -- 🗡️ 補題6: 左分配
  sum-distribˡ-lemma : ∀ n (c : Carrier) (f : ℕ → Carrier) → c * (finiteSum R f n) ≡ finiteSum R (λ k → c * f k) n
  sum-distribˡ-lemma zero c f = refl
  sum-distribˡ-lemma (suc n) c f =
    R-distribˡ c (finiteSum R f n) (f (suc n))
    ∙ cong (λ x → x + (c * f (suc n))) (sum-distribˡ-lemma n c f)

  -- ======================================================================
  -- 🗡️ [ラスボス：実体化フェーズ]
  -- ======================================================================
  double-sum-swap-lemma : (n : ℕ) (F : ℕ → ℕ → Carrier) → 
    finiteSum R (λ i → finiteSum R (λ j → F j (i ∸ j)) i) n 
    ≡ finiteSum R (λ k → finiteSum R (λ m → F k m) (n ∸ k)) n
  double-sum-swap-lemma zero F = refl
  double-sum-swap-lemma (suc n) F = 
    begin
      finiteSum R (λ i → finiteSum R (λ j → F j (i ∸ j)) i) n 
      + finiteSum R (λ j → F j (suc n ∸ j)) (suc n)
    ≡⟨ cong (λ x → x + finiteSum R (λ j → F j (suc n ∸ j)) (suc n)) (double-sum-swap-lemma n F) ⟩
      finiteSum R (λ k → finiteSum R (λ m → F k m) (n ∸ k)) n 
      + finiteSum R (λ j → F j (suc n ∸ j)) (suc n)
    ≡⟨ refl ⟩
      finiteSum R (λ k → finiteSum R (λ m → F k m) (n ∸ k)) n 
      + (finiteSum R (λ j → F j (suc n ∸ j)) n + F (suc n) (suc n ∸ suc n))
    ≡⟨ cong (λ x → finiteSum R (λ k → finiteSum R (λ m → F k m) (n ∸ k)) n 
                    + (finiteSum R (λ j → F j (suc n ∸ j)) n + F (suc n) x)) 
            (n∸n≡0 (suc n)) ⟩
      finiteSum R (λ k → finiteSum R (λ m → F k m) (n ∸ k)) n 
      + (finiteSum R (λ j → F j (suc n ∸ j)) n + F (suc n) 0)
    -- 【修正】sym を追加！
    ≡⟨ sym (+R-assoc (finiteSum R (λ k → finiteSum R (λ m → F k m) (n ∸ k)) n) 
                      (finiteSum R (λ j → F j (suc n ∸ j)) n) 
                      (F (suc n) 0)) ⟩
      (finiteSum R (λ k → finiteSum R (λ m → F k m) (n ∸ k)) n 
       + finiteSum R (λ j → F j (suc n ∸ j)) n) 
      + F (suc n) 0
    ≡⟨ cong (λ x → x + F (suc n) 0) (sym (sum-plus-sum n _ _)) ⟩
      finiteSum R (λ k → finiteSum R (λ m → F k m) (n ∸ k) + F k (suc n ∸ k)) n 
      + F (suc n) 0
    ≡⟨ cong (λ x → x + F (suc n) 0) (finiteSum-ext n _ _ (λ k k≤n → 
         cong₂ _+_ refl (cong (F k) (suc-∸-lemma n k k≤n)))) ⟩
      finiteSum R (λ k → finiteSum R (λ m → F k m) (n ∸ k) + F k (suc (n ∸ k))) n 
      + F (suc n) 0
    ≡⟨ refl ⟩
       finiteSum R (λ k → finiteSum R (λ m → F k m) (suc (n ∸ k))) n 
       + F (suc n) 0
    ≡⟨ cong (λ x → x + F (suc n) 0) (finiteSum-ext n _ _ (λ k k≤n → 
         cong (finiteSum R (λ m → F k m)) (sym (suc-∸-lemma n k k≤n)))) ⟩
       finiteSum R (λ k → finiteSum R (λ m → F k m) (suc n ∸ k)) n 
       + F (suc n) 0
    ≡⟨ cong (λ x → finiteSum R (λ k → finiteSum R (λ m → F k m) (suc n ∸ k)) n + x) 
            (sym (cong (finiteSum R (λ m → F (suc n) m)) (n∸n≡0 n))) ⟩
       finiteSum R (λ k → finiteSum R (λ m → F k m) (suc n ∸ k)) n 
       + finiteSum R (λ m → F (suc n) m) (n ∸ n)
    ≡⟨ refl ⟩
       finiteSum R (λ k → finiteSum R (λ m → F k m) (suc n ∸ k)) (suc n)
    ∎

  -- ======================================================================
  -- 3. 💥 最終定理：アソシエータ Φ のメインパス（三分割構成）
  -- ======================================================================

  -- 🗡️ Block 1: 分配フェーズ
  assoc-distrib : ∀ (A B C : FormalPowerSeries R) →
    cauchy R (cauchy R A B) C ≡ 
    (λ n → finiteSum R (λ i → finiteSum R (λ j → (A j * B (i ∸ j)) * C (n ∸ i)) i) n)
  assoc-distrib A B C = funExt λ n → 
    cong (λ F → finiteSum R F n) (funExt λ i → sum-distribʳ-lemma i (C (n ∸ i)) (λ j → A j * B (i ∸ j)))

  -- 🗡️ Block 2: 結合律適用フェーズ
  assoc-proof : ∀ (A B C : FormalPowerSeries R) →
    (λ n → finiteSum R (λ i → finiteSum R (λ j → (A j * B (i ∸ j)) * C (n ∸ i)) i) n) ≡
    (λ n → finiteSum R (λ i → finiteSum R (λ j → A j * (B (i ∸ j) * C (n ∸ i))) i) n)
  assoc-proof A B C = funExt λ n → 
    cong (λ F → finiteSum R F n) (funExt λ i → cong (λ G → finiteSum R G i) (funExt λ j → *R-assoc (A j) (B (i ∸ j)) (C (n ∸ i))))

  -- 🗡️ Block 3: 再構成フェーズ
  assoc-block3 : ∀ (A B C : FormalPowerSeries R) →
    (λ n → finiteSum R (λ i → finiteSum R (λ j → A j * (B (i ∸ j) * C (n ∸ i))) i) n) ≡
    cauchy R A (cauchy R B C)
  assoc-block3 A B C = funExt λ n → begin
    finiteSum R (λ i → finiteSum R (λ j → A j * (B (i ∸ j) * C (n ∸ i))) i) n
    ≡⟨ cong (λ F → finiteSum R F n) (funExt λ i → finiteSum-ext i _ _ (λ j j≤i → cong (λ X → A j * (B (i ∸ j) * C (n ∸ X))) (sym (+-∸-assoc-lemma i j j≤i)))) ⟩
    finiteSum R (λ i → finiteSum R (λ j → A j * (B (i ∸ j) * C (n ∸ (j +ℕ (i ∸ j))))) i) n
    ≡⟨ double-sum-swap-lemma n (λ k m → A k * (B m * C (n ∸ (k +ℕ m)))) ⟩
    finiteSum R (λ k → finiteSum R (λ m → A k * (B m * C (n ∸ (k +ℕ m)))) (n ∸ k)) n
    ≡⟨ cong (λ F → finiteSum R F n) (funExt λ k → sym (sum-distribˡ-lemma (n ∸ k) (A k) (λ m → B m * C (n ∸ (k +ℕ m))))) ⟩
    finiteSum R (λ k → A k * finiteSum R (λ m → B m * C (n ∸ (k +ℕ m))) (n ∸ k)) n
    ≡⟨ cong (λ F → finiteSum R F n) (funExt λ k → cong (λ X → A k * X) (cong (λ G → finiteSum R G (n ∸ k)) (funExt λ m → cong (λ Y → B m * C Y) (∸-dist-lemma n k m)))) ⟩
    finiteSum R (λ k → A k * finiteSum R (λ m → B m * C ((n ∸ k) ∸ m)) (n ∸ k)) n
    ≡⟨ refl ⟩
    cauchy R A (cauchy R B C) n ∎

  -- 👑 最終定理：3つの標識を繋いで一本の道にする
  cauchy-assoc : ∀ (A B C : FormalPowerSeries R) → 
    cauchy R (cauchy R A B) C ≡ cauchy R A (cauchy R B C)
  cauchy-assoc A B C = assoc-distrib A B C ∙ assoc-proof A B C ∙ assoc-block3 A B C