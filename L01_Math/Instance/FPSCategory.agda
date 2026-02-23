{-# OPTIONS --cubical --safe --guardedness #-}

module UMIN.L01_Math.Instance.FPSCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws as GL
open import Cubical.Foundations.Function hiding (_∘_)
open import Cubical.Foundations.Path using (Square→compPath)
open import Cubical.Data.Nat using (ℕ; _∸_; zero; suc) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order using (_≤_; zero-≤; ≤-refl)

open import UMIN.L00_Core.Logic.WeakMonoidalCategory
open import UMIN.L00_Core.FPS.CauchyAssoc

-- 🔹 自作等式変形エンジン（名前を衝突回避版に変更）
infix  3 _∎⇒
infixr 2 _≡⟨_⟩⇒_
infix  1 begin⇒_

begin⇒_ : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ≡ y → x ≡ y
begin⇒_ p = p

_≡⟨_⟩⇒_ : ∀ {ℓ} {A : Type ℓ} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩⇒ q = p ∙ q

_∎⇒ : ∀ {ℓ} {A : Type ℓ} (x : A) → x ≡ x
x ∎⇒ = refl

------------------------------------------------------------------------
-- FPS モジュール
------------------------------------------------------------------------

module FPSInstance {ℓ} (R : Ring ℓ) where
  open CauchyProofs R
  open Ring R

  -- 🔹 パスの積（*P）
  _*P_ : ∀ {a b c d : Carrier} → a ≡ b → c ≡ d → (a * c) ≡ (b * d)
  f *P g = cong₂ _*_ f g

  -- 🔹 乗法版の「正方形から compPath への変換」
  private
    *-square : ∀ (a b v w : Carrier) (p : a ≡ b) (s : v ≡ w) →
      (cong (a *_) s) ∙ (cong (λ x → x * w) p) ≡ (cong (λ x → x * v) p) ∙ (cong (b *_) s)
    *-square a b v w p s = sym (Square→compPath (λ i j → p i * s j))

  -- 🔹 *P とパス合成の可換性（Interchange Law）
  --    (p1 ∙ p2) *P (q1 ∙ q2) ≡ (p1 *P q1) ∙ (p2 *P q2)
  *P-∙ : ∀ (a b c u v w : Carrier)
    (p1 : a ≡ b) (p2 : b ≡ c)
    (q1 : u ≡ v) (q2 : v ≡ w) →
    (p1 ∙ p2) *P (q1 ∙ q2) ≡ (p1 *P q1) ∙ (p2 *P q2)
  *P-∙ a b c u v w p1 p2 q1 q2 =
    begin⇒_
      (p1 ∙ p2) *P (q1 ∙ q2)
    ≡⟨ GL.cong₂Funct _*_ (p1 ∙ p2) (q1 ∙ q2) ⟩⇒
      (cong (λ x → x * u) (p1 ∙ p2)) ∙ (cong (c *_) (q1 ∙ q2))
    ≡⟨ (λ i → (GL.cong-∙ (λ x → x * u) p1 p2 i) ∙ (GL.cong-∙ (c *_) q1 q2 i)) ⟩⇒
      ((cong (λ x → x * u) p1 ∙ cong (λ x → x * u) p2)
        ∙ (cong (c *_) q1 ∙ cong (c *_) q2))
    ≡⟨ (GL.assoc (cong (λ x → x * u) p1 ∙ cong (λ x → x * u) p2)
                  (cong (c *_) q1)
                  (cong (c *_) q2))
       ∙ cong (_∙ cong (c *_) q2)
              (sym (GL.assoc (cong (λ x → x * u) p1)
                              (cong (λ x → x * u) p2)
                              (cong (c *_) q1))) ⟩⇒
      (cong (λ x → x * u) p1 ∙ (cong (λ x → x * u) p2 ∙ cong (c *_) q1))
        ∙ cong (c *_) q2
    ≡⟨ cong (λ φ → (cong (λ x → x * u) p1 ∙ φ) ∙ cong (c *_) q2)
             (sym (*-square b c u v p2 q1)) ⟩⇒
      (cong (λ x → x * u) p1 ∙ (cong (b *_) q1 ∙ cong (λ x → x * v) p2))
        ∙ cong (c *_) q2
    ≡⟨ cong (_∙ cong (c *_) q2)
             (GL.assoc (cong (λ x → x * u) p1)
                       (cong (b *_) q1)
                       (cong (λ x → x * v) p2)) ⟩⇒
      ((cong (λ x → x * u) p1 ∙ cong (b *_) q1)
        ∙ cong (λ x → x * v) p2) ∙ cong (c *_) q2
    ≡⟨ sym (GL.assoc ((cong (λ x → x * u) p1) ∙ (cong (b *_) q1))
                      (cong (λ x → x * v) p2)
                      (cong (c *_) q2)) ⟩⇒
      (cong (λ x → x * u) p1 ∙ cong (b *_) q1)
        ∙ (cong (λ x → x * v) p2 ∙ cong (c *_) q2)
    ≡⟨ (λ i → (sym (GL.cong₂Funct _*_ p1 q1) i)
               ∙ (sym (GL.cong₂Funct _*_ p2 q2) i)) ⟩⇒
      (p1 *P q1) ∙ (p2 *P q2)
    ∎⇒

  -- 🔹 加法版の「正方形から compPath への変換」
  private
    +-square : ∀ (a b v w : Carrier) (p : a ≡ b) (s : v ≡ w) →
      (cong (a +_) s) ∙ (cong (λ x → x + w) p) ≡ (cong (λ x → x + v) p) ∙ (cong (b +_) s)
    +-square a b v w p s = sym (Square→compPath (λ i j → p i + s j))

  -- 🔹 +-interchange（垂直合成と加法の交換律）
  -- (p ∙ q) + (r ∙ s) ≡ (p + r) ∙ (q + s)
  +-interchange : ∀ (a b c u v w : Carrier)
    (p : a ≡ b) (q : b ≡ c) (r : u ≡ v) (s : v ≡ w) →
    cong₂ _+_ (p ∙ q) (r ∙ s) ≡ (cong₂ _+_ p r) ∙ (cong₂ _+_ q s)
  +-interchange a b c u v w p q r s =
    begin⇒_
      (cong₂ (_+_) (p ∙ q) (r ∙ s))
    ≡⟨ GL.cong₂Funct _+_ (p ∙ q) (r ∙ s) ⟩⇒
      (cong (λ x → x + u) (p ∙ q)) ∙ (cong (c +_) (r ∙ s))
    ≡⟨ (λ i → (GL.cong-∙ (λ x → x + u) p q i) ∙ (GL.cong-∙ (c +_) r s i)) ⟩⇒
      ((cong (λ x → x + u) p ∙ cong (λ x → x + u) q) ∙ (cong (c +_) r ∙ cong (c +_) s))
    ≡⟨ (GL.assoc (cong (λ x → x + u) p ∙ cong (λ x → x + u) q) (cong (c +_) r) (cong (c +_) s))
       ∙ (cong (_∙ cong (c +_) s)
               (sym (GL.assoc (cong (λ x → x + u) p)
                              (cong (λ x → x + u) q)
                              (cong (c +_) r)))) ⟩⇒
      (cong (λ x → x + u) p ∙ (cong (λ x → x + u) q ∙ cong (c +_) r)) ∙ cong (c +_) s
    ≡⟨ cong (λ φ → (cong (λ x → x + u) p ∙ φ) ∙ cong (c +_) s)
             (sym (+-square b c u v q r)) ⟩⇒
      (cong (λ x → x + u) p ∙ (cong (b +_) r ∙ cong (λ x → x + v) q)) ∙ cong (c +_) s
    ≡⟨ cong (_∙ cong (c +_) s)
             (GL.assoc (cong (λ x → x + u) p)
                       (cong (b +_) r)
                       (cong (λ x → x + v) q)) ⟩⇒
      ((cong (λ x → x + u) p ∙ cong (b +_) r) ∙ cong (λ x → x + v) q) ∙ cong (c +_) s
    ≡⟨ sym (GL.assoc ((cong (λ x → x + u) p) ∙ (cong (b +_) r))
                    (cong (λ x → x + v) q)
                    (cong (c +_) s)) ⟩⇒
      (cong (λ x → x + u) p ∙ cong (b +_) r) ∙ (cong (λ x → x + v) q ∙ cong (c +_) s)
    ≡⟨ (λ i → (sym (GL.cong₂Funct _+_ p r) i)
               ∙ (sym (GL.cong₂Funct _+_ q s) i)) ⟩⇒
      (cong₂ _+_ p r) ∙ (cong₂ _+_ q s)
    ∎⇒

  -- 🔹 finiteSum-ext が点ごとの ∙ を分配
  finiteSum-ext-∙ : ∀ n (f g h : ℕ → Carrier)
    (hyp1 : ∀ k → k ≤ n → f k ≡ g k)
    (hyp2 : ∀ k → k ≤ n → g k ≡ h k) →
    finiteSum-ext n f h (λ k k≤n → hyp1 k k≤n ∙ hyp2 k k≤n)
    ≡ (finiteSum-ext n f g hyp1) ∙ (finiteSum-ext n g h hyp2)
  finiteSum-ext-∙ zero f g h hyp1 hyp2 = refl
  finiteSum-ext-∙ (suc n) f g h hyp1 hyp2 =
    begin⇒_
      (finiteSum-ext (suc n) f h (λ k k≤n → hyp1 k k≤n ∙ hyp2 k k≤n))
    ≡⟨ refl ⟩⇒
      cong₂ _+_
        (finiteSum-ext n f h (λ k k≤n → hyp1 k (suc-≤ k≤n) ∙ hyp2 k (suc-≤ k≤n)))
        (hyp1 (suc n) ≤-refl ∙ hyp2 (suc n) ≤-refl)
    ≡⟨ cong (λ x →
               cong₂ _+_ x (hyp1 (suc n) ≤-refl ∙ hyp2 (suc n) ≤-refl))
             (finiteSum-ext-∙ n f g h
               (λ k k≤n → hyp1 k (suc-≤ k≤n))
               (λ k k≤n → hyp2 k (suc-≤ k≤n))) ⟩⇒
      cong₂ _+_
        (finiteSum-ext n f g (λ k k≤n → hyp1 k (suc-≤ k≤n))
           ∙ finiteSum-ext n g h (λ k k≤n → hyp2 k (suc-≤ k≤n)))
        (hyp1 (suc n) ≤-refl ∙ hyp2 (suc n) ≤-refl)
    ≡⟨ +-interchange
          (finiteSum R f n) (finiteSum R g n) (finiteSum R h n)
          (f (suc n)) (g (suc n)) (h (suc n))
          (finiteSum-ext n f g (λ k k≤n → hyp1 k (suc-≤ k≤n)))
          (finiteSum-ext n g h (λ k k≤n → hyp2 k (suc-≤ k≤n)))
          (hyp1 (suc n) ≤-refl) (hyp2 (suc n) ≤-refl) ⟩⇒
      (cong₂ _+_ (finiteSum-ext n f g (λ k k≤n → hyp1 k (suc-≤ k≤n)))
                 (hyp1 (suc n) ≤-refl))
        ∙ (cong₂ _+_ (finiteSum-ext n g h (λ k k≤n → hyp2 k (suc-≤ k≤n)))
                    (hyp2 (suc n) ≤-refl))
    ≡⟨ refl ⟩⇒
      (finiteSum-ext (suc n) f g hyp1) ∙ (finiteSum-ext (suc n) g h hyp2)
    ∎⇒
    where
      suc-≤ : ∀ {m n} → m ≤ n → m ≤ suc n
      suc-≤ (k , p) = (suc k) , cong suc p

  -- 🔹 tensorHom の実体（射 f と g をテンソル積で合成する操作）
  tensorHom-impl : ∀ {A B C D : FormalPowerSeries R}
    (f : ∀ n → A n ≡ B n) (g : ∀ n → C n ≡ D n) →
    ∀ n → cauchy R A C n ≡ cauchy R B D n
  tensorHom-impl {A} {B} {C} {D} f g n =
    finiteSum-ext n (λ k → A k * C (n ∸ k)) (λ k → B k * D (n ∸ k)) (λ k _ → f k *P g (n ∸ k))

  -- 🔹 補題：refl（動かないパス）を足し合わせたものは、結局reflになる
  finiteSum-ext-refl : ∀ n (f : ℕ → Carrier) → 
    finiteSum-ext n f f (λ k _ → refl) ≡ refl
  finiteSum-ext-refl zero f = refl
  finiteSum-ext-refl (suc n) f = cong (λ p → cong₂ _+_ p refl) (finiteSum-ext-refl n f)

  -- 🔹 tensor-id-impl （🗡️ ?0 の試練、攻略完了！）
  tensor-id-impl : ∀ {A B : FormalPowerSeries R} →
    tensorHom-impl {A} {A} {B} {B} (λ n → refl) (λ n → refl) ≡ (λ n → refl)
  tensor-id-impl {A} {B} = funExt λ n → finiteSum-ext-refl n (λ k → A k * B (n ∸ k))

  -- 🔹 tensor-comp-impl （🗡️ 次の試練 ?1 の場所）
  tensor-comp-impl :
    ∀ {A B C D E F : FormalPowerSeries R}
    (f1 : ∀ n → A n ≡ B n) (f2 : ∀ n → B n ≡ C n)
    (g1 : ∀ n → D n ≡ E n) (g2 : ∀ n → E n ≡ F n) →
    tensorHom-impl (λ n → f1 n ∙ f2 n) (λ n → g1 n ∙ g2 n) ≡
    (λ n → tensorHom-impl f1 g1 n ∙ tensorHom-impl f2 g2 n)
  tensor-comp-impl {A} {B} {C} {D} {E} {F} f1 f2 g1 g2 =
    funExt λ n →
      begin⇒_
        (finiteSum-ext n (λ k → A k * D (n ∸ k)) (λ k → C k * F (n ∸ k)) 
          (λ k _ → (f1 k ∙ f2 k) *P (g1 (n ∸ k) ∙ g2 (n ∸ k))))
      ≡⟨ cong (finiteSum-ext n (λ k → A k * D (n ∸ k)) (λ k → C k * F (n ∸ k)))
              (funExt (λ k → funExt (λ _ → *P-∙ (A k) (B k) (C k) (D (n ∸ k)) (E (n ∸ k)) (F (n ∸ k))
                                        (f1 k) (f2 k) (g1 (n ∸ k)) (g2 (n ∸ k))))) ⟩⇒
        finiteSum-ext n (λ k → A k * D (n ∸ k)) (λ k → C k * F (n ∸ k))
          (λ k _ → (f1 k *P g1 (n ∸ k)) ∙ (f2 k *P g2 (n ∸ k)))
      ≡⟨ finiteSum-ext-∙ n (λ k → A k * D (n ∸ k)) (λ k → B k * E (n ∸ k)) (λ k → C k * F (n ∸ k))
            (λ k _ → f1 k *P g1 (n ∸ k)) (λ k _ → f2 k *P g2 (n ∸ k)) ⟩⇒
        (tensorHom-impl f1 g1 n) ∙ (tensorHom-impl f2 g2 n)
      ∎⇒

  ------------------------------------------------------------------------
  -- cauchy-assoc を 3 ブロックに分解するための補助パス（関数レベル）
  ------------------------------------------------------------------------
  private
    -- 🗡️ 分解証明（変更なし）
    assoc-distrib-path : ∀ (X Y Z : FormalPowerSeries R) →
      cauchy-assoc X Y Z ≡ (assoc-distrib X Y Z ∙ assoc-proof X Y Z ∙ assoc-block3 X Y Z)
    assoc-distrib-path X Y Z = refl

    -- =======================================================================
    -- 🌌 1. 中継宇宙の定義（二重和の階層構造を復元）
    -- =======================================================================
    tensor-int1 : (A B C : FormalPowerSeries R) → ℕ → Carrier
    tensor-int1 A B C n = finiteSum R (λ i → finiteSum R (λ j → (A j * B (i ∸ j)) * C (n ∸ i)) i) n

    morph-int1 : ∀ {A A' B B' C C' : FormalPowerSeries R} 
      (f : ∀ n → A n ≡ A' n) (g : ∀ n → B n ≡ B' n) (h : ∀ n → C n ≡ C' n) n →
      tensor-int1 A B C n ≡ tensor-int1 A' B' C' n
    morph-int1 {A} {A'} {B} {B'} {C} {C'} f g h n = 
      finiteSum-ext n 
        (λ i → finiteSum R (λ j → (A j * B (i ∸ j)) * C (n ∸ i)) i)  
        (λ i → finiteSum R (λ j → (A' j * B' (i ∸ j)) * C' (n ∸ i)) i) 
        (λ i _ → finiteSum-ext i 
           (λ j → (A j * B (i ∸ j)) * C (n ∸ i)) 
           (λ j → (A' j * B' (i ∸ j)) * C' (n ∸ i)) 
           (λ j _ → (f j *P g (i ∸ j)) *P h (n ∸ i)))

    tensor-int2 : (A B C : FormalPowerSeries R) → ℕ → Carrier
    tensor-int2 A B C n = finiteSum R (λ i → finiteSum R (λ j → A j * (B (i ∸ j) * C (n ∸ i))) i) n

    morph-int2 : ∀ {A A' B B' C C' : FormalPowerSeries R} (f : ∀ n → A n ≡ A' n) (g : ∀ n → B n ≡ B' n) (h : ∀ n → C n ≡ C' n) n →
      tensor-int2 A B C n ≡ tensor-int2 A' B' C' n
    morph-int2 {A} {A'} {B} {B'} {C} {C'} f g h n = 
      finiteSum-ext n 
        (λ i → finiteSum R (λ j → A j * (B (i ∸ j) * C (n ∸ i))) i)
        (λ i → finiteSum R (λ j → A' j * (B' (i ∸ j) * C' (n ∸ i))) i)
        (λ i _ → finiteSum-ext i 
           (λ j → A j * (B (i ∸ j) * C (n ∸ i)))
           (λ j → A' j * (B' (i ∸ j) * C' (n ∸ i)))
           (λ j _ → f j *P (g (i ∸ j) *P h (n ∸ i))))

    -- =======================================================================
    -- 🌌 2. 次元降下補題（関数パスを成分パスへ）
    -- =======================================================================
    assoc-applied : ∀ X Y Z n →
      (λ i → (assoc-distrib X Y Z ∙ assoc-proof X Y Z ∙ assoc-block3 X Y Z) i n) ≡
      ((λ i → assoc-distrib X Y Z i n) ∙ ((λ i → assoc-proof X Y Z i n) ∙ (λ i → assoc-block3 X Y Z i n)))
    assoc-applied X Y Z n =
      begin⇒_
        (λ i → (assoc-distrib X Y Z ∙ (assoc-proof X Y Z ∙ assoc-block3 X Y Z)) i n)
      ≡⟨ GL.cong-∙ (λ F → F n) (assoc-distrib X Y Z) (assoc-proof X Y Z ∙ assoc-block3 X Y Z) ⟩⇒
        ((λ i → assoc-distrib X Y Z i n) ∙ (λ i → (assoc-proof X Y Z ∙ assoc-block3 X Y Z) i n))
      ≡⟨ cong (λ p → (λ i → assoc-distrib X Y Z i n) ∙ p)
              (GL.cong-∙ (λ F → F n) (assoc-proof X Y Z) (assoc-block3 X Y Z)) ⟩⇒
        ((λ i → assoc-distrib X Y Z i n) ∙ ((λ i → assoc-proof X Y Z i n) ∙ (λ i → assoc-block3 X Y Z i n)))
      ∎⇒

    -- =======================================================================
    -- 🌉 3. 境界を繋ぐ「高次ワープ・エンジン」（数珠繋ぎ eval 補題）
    -- =======================================================================
    finiteSum-ext-eval : ∀ n (F : ℕ → I → Carrier) → 
      (λ i → finiteSum-ext n (λ k → F k i0) (λ k → F k i1) (λ k _ i_idx → F k i_idx) i) ≡ (λ i → finiteSum R (λ k → F k i) n)
    finiteSum-ext-eval zero F = refl
    finiteSum-ext-eval (suc n) F j i = (finiteSum-ext-eval n F j i) + (F (suc n) i)

    tensorHom-eval : ∀ {A A' B B'} (f : ∀ n → A n ≡ A' n) (g : ∀ n → B n ≡ B' n) n →
      tensorHom-impl f g n ≡ (λ i → cauchy R (λ k → f k i) (λ k → g k i) n)
    tensorHom-eval f g n = finiteSum-ext-eval n (λ k i → f k i * g (n ∸ k) i)

    tensorHom-double-eval : ∀ {A A' B B' C C'} (f : ∀ n → A n ≡ A' n) (g : ∀ n → B n ≡ B' n) (h : ∀ n → C n ≡ C' n) n →
      tensorHom-impl (tensorHom-impl f g) h n ≡ (λ i → cauchy R (λ k → cauchy R (λ j → f j i) (λ j → g j i) k) (λ k → h k i) n)
    tensorHom-double-eval f g h n = p1 ∙ p2
      where
        p1 = finiteSum-ext-eval n (λ k i → tensorHom-impl f g k i * h (n ∸ k) i)
        p2 = λ j i → finiteSum R (λ k → tensorHom-eval f g k j i * h (n ∸ k) i) n

    morph-int1-eval : ∀ {A A' B B' C C'} (f : ∀ n → A n ≡ A' n) (g : ∀ n → B n ≡ B' n) (h : ∀ n → C n ≡ C' n) n →
      morph-int1 f g h n ≡ (λ i → tensor-int1 (λ k → f k i) (λ k → g k i) (λ k → h k i) n)
    morph-int1-eval f g h n = p1 ∙ p2
      where
        p1 = finiteSum-ext-eval n (λ k i → finiteSum-ext k _ _ (λ m _ i_idx → (f m i_idx * g (k ∸ m) i_idx) * h (n ∸ k) i_idx) i)
        p2 = λ j i → finiteSum R (λ k → finiteSum-ext-eval k (λ m i_idx → (f m i_idx * g (k ∸ m) i_idx) * h (n ∸ k) i_idx) j i) n

    morph-int2-eval : ∀ {A A' B B' C C'} (f : ∀ n → A n ≡ A' n) (g : ∀ n → B n ≡ B' n) (h : ∀ n → C n ≡ C' n) n →
      morph-int2 f g h n ≡ (λ i → tensor-int2 (λ k → f k i) (λ k → g k i) (λ k → h k i) n)
    morph-int2-eval f g h n = p1 ∙ p2
      where
        p1 = finiteSum-ext-eval n (λ k i → finiteSum-ext k _ _ (λ m _ i_idx → f m i_idx * (g (k ∸ m) i_idx * h (n ∸ k) i_idx)) i)
        p2 = λ j i → finiteSum R (λ k → finiteSum-ext-eval k (λ m i_idx → f m i_idx * (g (k ∸ m) i_idx * h (n ∸ k) i_idx)) j i) n

    tensorHom-right-eval : ∀ {A A' B B' C C'} (f : ∀ n → A n ≡ A' n) (g : ∀ n → B n ≡ B' n) (h : ∀ n → C n ≡ C' n) n →
      tensorHom-impl f (tensorHom-impl g h) n ≡ (λ i → cauchy R (λ k → f k i) (λ k → cauchy R (λ j → g j i) (λ j → h j i) k) n)
    tensorHom-right-eval f g h n = p1 ∙ p2
      where
        p1 = finiteSum-ext-eval n (λ k i → f k i * tensorHom-impl g h (n ∸ k) i)
        p2 = λ j i → finiteSum R (λ k → f k i * tensorHom-eval g h (n ∸ k) j i) n

    -- =======================================================================
    -- 🚀 4. 独立補題の証明（完全接続版）
    -- =======================================================================
    warp-block1 : ∀ (A A' B B' C C' : FormalPowerSeries R) 
      (f : ∀ n → A n ≡ A' n) (g : ∀ n → B n ≡ B' n) (h : ∀ n → C n ≡ C' n) n →
      (tensorHom-impl (tensorHom-impl f g) h n ∙ (λ i → assoc-distrib A' B' C' i n)) ≡
      ((λ i → assoc-distrib A B C i n) ∙ morph-int1 f g h n)
    warp-block1 A A' B B' C C' f g h n = 
      begin⇒_
        (tensorHom-impl (tensorHom-impl f g) h n ∙ (λ i → assoc-distrib A' B' C' i n))
      ≡⟨ cong (λ φ → φ ∙ (λ i → assoc-distrib A' B' C' i n)) (tensorHom-double-eval f g h n) ⟩⇒
        ((λ i → cauchy R (λ k → cauchy R (λ j → f j i) (λ j → g j i) k) (λ k → h k i) n) ∙ (λ i → assoc-distrib A' B' C' i n))
      ≡⟨ Square→compPath (λ i j → assoc-distrib (λ k → f k i) (λ k → g k i) (λ k → h k i) j n) ⟩⇒
        ((λ i → assoc-distrib A B C i n) ∙ (λ i → tensor-int1 (λ k → f k i) (λ k → g k i) (λ k → h k i) n))
      ≡⟨ cong ((λ i → assoc-distrib A B C i n) ∙_) (sym (morph-int1-eval f g h n)) ⟩⇒
        ((λ i → assoc-distrib A B C i n) ∙ morph-int1 f g h n)
      ∎⇒

    warp-block2 : ∀ (A A' B B' C C' : FormalPowerSeries R) 
      (f : ∀ n → A n ≡ A' n) (g : ∀ n → B n ≡ B' n) (h : ∀ n → C n ≡ C' n) n →
      (morph-int1 f g h n ∙ (λ i → assoc-proof A' B' C' i n)) ≡
      ((λ i → assoc-proof A B C i n) ∙ morph-int2 f g h n)
    warp-block2 A A' B B' C C' f g h n = 
      begin⇒_
        (morph-int1 f g h n ∙ (λ i → assoc-proof A' B' C' i n))
      ≡⟨ cong (_∙ (λ i → assoc-proof A' B' C' i n)) (morph-int1-eval f g h n) ⟩⇒
        ((λ i → tensor-int1 (λ k → f k i) (λ k → g k i) (λ k → h k i) n) ∙ (λ i → assoc-proof A' B' C' i n))
      ≡⟨ Square→compPath (λ i j → assoc-proof (λ k → f k i) (λ k → g k i) (λ k → h k i) j n) ⟩⇒
        ((λ i → assoc-proof A B C i n) ∙ (λ i → tensor-int2 (λ k → f k i) (λ k → g k i) (λ k → h k i) n))
      ≡⟨ cong ((λ i → assoc-proof A B C i n) ∙_) (sym (morph-int2-eval f g h n)) ⟩⇒
        ((λ i → assoc-proof A B C i n) ∙ morph-int2 f g h n)
      ∎⇒

    warp-block3 : ∀ (A A' B B' C C' : FormalPowerSeries R) 
      (f : ∀ n → A n ≡ A' n) (g : ∀ n → B n ≡ B' n) (h : ∀ n → C n ≡ C' n) n →
      (morph-int2 f g h n ∙ (λ i → assoc-block3 A' B' C' i n)) ≡
      ((λ i → assoc-block3 A B C i n) ∙ tensorHom-impl f (tensorHom-impl g h) n)
    warp-block3 A A' B B' C C' f g h n = 
      begin⇒_
        (morph-int2 f g h n ∙ (λ i → assoc-block3 A' B' C' i n))
      ≡⟨ cong (_∙ (λ i → assoc-block3 A' B' C' i n)) (morph-int2-eval f g h n) ⟩⇒
        ((λ i → tensor-int2 (λ k → f k i) (λ k → g k i) (λ k → h k i) n) ∙ (λ i → assoc-block3 A' B' C' i n))
      ≡⟨ Square→compPath (λ i j → assoc-block3 (λ k → f k i) (λ k → g k i) (λ k → h k i) j n) ⟩⇒
        ((λ i → assoc-block3 A B C i n) ∙ (λ i → cauchy R (λ k → f k i) (λ k → cauchy R (λ j → g j i) (λ j → h j i) k) n))
      ≡⟨ cong ((λ i → assoc-block3 A B C i n) ∙_) (sym (tensorHom-right-eval f g h n)) ⟩⇒
        ((λ i → assoc-block3 A B C i n) ∙ tensorHom-impl f (tensorHom-impl g h) n)
      ∎⇒

    -- =======================================================================
    -- 🗡️ 5. 変化のワープ（主定理）
    -- =======================================================================
    warp-double-sum : ∀ {A A' B B' C C' : FormalPowerSeries R}
      (f : ∀ n → A n ≡ A' n) (g : ∀ n → B n ≡ B' n) (h : ∀ n → C n ≡ C' n) n →
      (tensorHom-impl (tensorHom-impl f g) h n ∙ 
        (λ i → (assoc-distrib A' B' C' ∙ assoc-proof A' B' C' ∙ assoc-block3 A' B' C') i n)) ≡
      ((λ i → (assoc-distrib A B C ∙ assoc-proof A B C ∙ assoc-block3 A B C) i n) ∙ 
        tensorHom-impl f (tensorHom-impl g h) n)
    warp-double-sum {A} {A'} {B} {B'} {C} {C'} f g h n = 
      begin⇒_
        (tensorHom-impl (tensorHom-impl f g) h n ∙ 
          (λ i → (assoc-distrib A' B' C' ∙ assoc-proof A' B' C' ∙ assoc-block3 A' B' C') i n))
      ≡⟨ cong (λ φ → tensorHom-impl (tensorHom-impl f g) h n ∙ φ) (assoc-applied A' B' C' n) ⟩⇒
        (tensorHom-impl (tensorHom-impl f g) h n ∙ (block1' ∙ (block2' ∙ block3')))
      ≡⟨ GL.assoc (tensorHom-impl (tensorHom-impl f g) h n) block1' (block2' ∙ block3') ⟩⇒
        ((tensorHom-impl (tensorHom-impl f g) h n ∙ block1') ∙ (block2' ∙ block3'))
      ≡⟨ cong (λ φ → φ ∙ (block2' ∙ block3')) (warp-block1 A A' B B' C C' f g h n) ⟩⇒
        ((block1 ∙ morph-int1 f g h n) ∙ (block2' ∙ block3'))
      ≡⟨ sym (GL.assoc block1 (morph-int1 f g h n) (block2' ∙ block3')) ⟩⇒
        (block1 ∙ (morph-int1 f g h n ∙ (block2' ∙ block3')))
      ≡⟨ cong (λ φ → block1 ∙ φ) (GL.assoc (morph-int1 f g h n) block2' block3') ⟩⇒
        (block1 ∙ ((morph-int1 f g h n ∙ block2') ∙ block3'))
      ≡⟨ cong (λ φ → block1 ∙ (φ ∙ block3')) (warp-block2 A A' B B' C C' f g h n) ⟩⇒
        (block1 ∙ ((block2 ∙ morph-int2 f g h n) ∙ block3'))
      ≡⟨ cong (λ φ → block1 ∙ φ) (sym (GL.assoc block2 (morph-int2 f g h n) block3')) ⟩⇒
        (block1 ∙ (block2 ∙ (morph-int2 f g h n ∙ block3')))
      ≡⟨ cong (λ φ → block1 ∙ (block2 ∙ φ)) (warp-block3 A A' B B' C C' f g h n) ⟩⇒
        (block1 ∙ (block2 ∙ (block3 ∙ tensorHom-impl f (tensorHom-impl g h) n)))
      ≡⟨ GL.assoc block1 block2 (block3 ∙ tensorHom-impl f (tensorHom-impl g h) n) ⟩⇒
        ((block1 ∙ block2) ∙ (block3 ∙ tensorHom-impl f (tensorHom-impl g h) n))
      ≡⟨ GL.assoc (block1 ∙ block2) block3 (tensorHom-impl f (tensorHom-impl g h) n) ⟩⇒
        (((block1 ∙ block2) ∙ block3) ∙ tensorHom-impl f (tensorHom-impl g h) n)
      ≡⟨ cong (λ φ → φ ∙ tensorHom-impl f (tensorHom-impl g h) n) (sym (GL.assoc block1 block2 block3)) ⟩⇒
        ((block1 ∙ (block2 ∙ block3)) ∙ tensorHom-impl f (tensorHom-impl g h) n)
      ≡⟨ cong (λ φ → φ ∙ tensorHom-impl f (tensorHom-impl g h) n) (sym (assoc-applied A B C n)) ⟩⇒
        ((λ i → (assoc-distrib A B C ∙ assoc-proof A B C ∙ assoc-block3 A B C) i n) ∙ 
        tensorHom-impl f (tensorHom-impl g h) n)
      ∎⇒
      where
        block1 = λ i → assoc-distrib A B C i n
        block1' = λ i → assoc-distrib A' B' C' i n
        block2 = λ i → assoc-proof A B C i n
        block2' = λ i → assoc-proof A' B' C' i n
        block3 = λ i → assoc-block3 A B C i n
        block3' = λ i → assoc-block3 A' B' C' i n

    -- =======================================================================
    -- 🛑 6. Φ の自然性
    -- =======================================================================
    Φ-natural-impl : ∀ {A A' B B' C C' : FormalPowerSeries R}
      (f : ∀ n → A n ≡ A' n) (g : ∀ n → B n ≡ B' n) (h : ∀ n → C n ≡ C' n) →
      (λ n → (tensorHom-impl (tensorHom-impl f g) h) n ∙ (λ i → cauchy-assoc A' B' C' i n)) ≡
      (λ n → (λ i → cauchy-assoc A B C i n) ∙ (tensorHom-impl f (tensorHom-impl g h)) n)
    Φ-natural-impl {A} {A'} {B} {B'} {C} {C'} f g h = funExt λ n →
      begin⇒_
        (tensorHom-impl (tensorHom-impl f g) h n ∙ (λ i → cauchy-assoc A' B' C' i n))
      ≡⟨ cong (λ φ → tensorHom-impl (tensorHom-impl f g) h n ∙ (λ i → φ i n)) 
              (assoc-distrib-path A' B' C') ⟩⇒ 
        (tensorHom-impl (tensorHom-impl f g) h n ∙ 
          (λ i → (assoc-distrib A' B' C' ∙ assoc-proof A' B' C' ∙ assoc-block3 A' B' C') i n))
      ≡⟨ warp-double-sum f g h n ⟩⇒
        ((λ i → (assoc-distrib A B C ∙ assoc-proof A B C ∙ assoc-block3 A B C) i n)
          ∙ tensorHom-impl f (tensorHom-impl g h) n)
      ≡⟨ cong (λ φ → (λ i → φ i n) ∙ tensorHom-impl f (tensorHom-impl g h) n) 
              (sym (assoc-distrib-path A B C)) ⟩⇒ 
        ((λ i → cauchy-assoc A B C i n) ∙ tensorHom-impl f (tensorHom-impl g h) n)
      ∎⇒

  -- =======================================================================
  -- 🛑 五角形の5つの辺の定義（一番安定する tensorHom-impl 版に復帰！）
  -- =======================================================================
  pentagon-p1 : ∀ A B C D n → cauchy R (cauchy R (cauchy R A B) C) D n ≡ cauchy R (cauchy R A (cauchy R B C)) D n
  pentagon-p1 A B C D n = tensorHom-impl (λ k i → cauchy-assoc A B C i k) (λ k _ → D k) n

  pentagon-p2 : ∀ A B C D n → cauchy R (cauchy R A (cauchy R B C)) D n ≡ cauchy R A (cauchy R (cauchy R B C) D) n
  pentagon-p2 A B C D n = λ i → cauchy-assoc A (cauchy R B C) D i n

  pentagon-p3 : ∀ A B C D n → cauchy R A (cauchy R (cauchy R B C) D) n ≡ cauchy R A (cauchy R B (cauchy R C D)) n
  pentagon-p3 A B C D n = tensorHom-impl (λ k _ → A k) (λ k i → cauchy-assoc B C D i k) n

  pentagon-q1 : ∀ A B C D n → cauchy R (cauchy R (cauchy R A B) C) D n ≡ cauchy R (cauchy R A B) (cauchy R C D) n
  pentagon-q1 A B C D n = λ i → cauchy-assoc (cauchy R A B) C D i n

  pentagon-q2 : ∀ A B C D n → cauchy R (cauchy R A B) (cauchy R C D) n ≡ cauchy R A (cauchy R B (cauchy R C D)) n
  pentagon-q2 A B C D n = λ i → cauchy-assoc A B (cauchy R C D) i n

  -- =======================================================================
  -- 🌌 1. 究極のハブ（Hub）：4つの数列の完全展開テンソル積（三重和）
  -- =======================================================================
  tensor-int-4way : (A B C D : FormalPowerSeries R) → ℕ → Carrier
  tensor-int-4way A B C D n = 
    finiteSum R (λ i → 
      finiteSum R (λ j → 
        finiteSum R (λ k → 
          (A k * B (j ∸ k)) * (C (i ∸ j) * D (n ∸ i))
        ) j
      ) i
    ) n
  
  -- =======================================================================
  -- 🛠️ 補助補題群：和に対する分配律
  -- =======================================================================
  
  -- 🔹 右分配律（Σ f * c ≡ Σ (f * c)）
  sum-distrib-r : ∀ n (f : ℕ → Carrier) (c : Carrier) → 
    finiteSum R f n * c ≡ finiteSum R (λ k → f k * c) n
  sum-distrib-r zero f c = refl
  sum-distrib-r (suc n) f c = 
    begin⇒
      (finiteSum R f n + f (suc n)) * c
    ≡⟨ R-distribʳ (finiteSum R f n) (f (suc n)) c ⟩⇒
      (finiteSum R f n * c) + (f (suc n) * c)
    ≡⟨ (λ i → sum-distrib-r n f c i + (f (suc n) * c)) ⟩⇒
      finiteSum R (λ k → f k * c) n + (f (suc n) * c)
    ∎⇒

  -- 🔹 左分配律（c * Σ f ≡ Σ (c * f)）
  sum-distrib-l : ∀ n (c : Carrier) (f : ℕ → Carrier) → 
    c * finiteSum R f n ≡ finiteSum R (λ k → c * f k) n
  sum-distrib-l zero c f = refl
  sum-distrib-l (suc n) c f = 
    begin⇒
      c * (finiteSum R f n + f (suc n))
    ≡⟨ R-distribˡ c (finiteSum R f n) (f (suc n)) ⟩⇒
      (c * finiteSum R f n) + (c * f (suc n))
    ≡⟨ (λ i → sum-distrib-l n c f i + (c * f (suc n))) ⟩⇒
      finiteSum R (λ k → c * f k) n + (c * f (suc n))
    ∎⇒

  -- 🔹 究極の防壁：Carrier が Set（集合）であることの抽出
  carrier-is-set : {x y : Carrier} (p q : x ≡ y) → p ≡ q
  carrier-is-set {x} {y} p q = Ring.is-set R x y p q

  -- =======================================================================
  -- 🎯 2. 5本のスポーク（完全隔離型 abstract・全直通ルート）
  -- =======================================================================
  abstract
    spoke-v1 : ∀ A B C D n → cauchy R (cauchy R (cauchy R A B) C) D n ≡ tensor-int-4way A B C D n
    spoke-v1 A B C D n = finiteSum-ext-eval n (λ i i_idx → 
      (sum-distrib-r i (λ j → cauchy R A B j * C (i ∸ j)) (D (n ∸ i)) ∙
       finiteSum-ext-eval i (λ j j_idx → 
         (*R-assoc (cauchy R A B j) (C (i ∸ j)) (D (n ∸ i)) ∙
          sum-distrib-r j (λ m → A m * B (j ∸ m)) (C (i ∸ j) * D (n ∸ i))) j_idx)) i_idx)

  abstract
    spoke-v2 : ∀ A B C D n → cauchy R (cauchy R A (cauchy R B C)) D n ≡ tensor-int-4way A B C D n
    spoke-v2 A B C D n = finiteSum-ext-eval n (λ i i_idx → 
      ((λ k → cauchy-assoc A B C k i * D (n ∸ i)) ∙
       (sum-distrib-r i (λ j → A j * cauchy R B C (i ∸ j)) (D (n ∸ i)) ∙
        finiteSum-ext-eval i (λ j j_idx → 
          *R-assoc (A j) (cauchy R B C (i ∸ j)) (D (n ∸ i)) j_idx))) i_idx)

  abstract
    spoke-v3 : ∀ A B C D n → cauchy R A (cauchy R (cauchy R B C) D) n ≡ tensor-int-4way A B C D n
    spoke-v3 A B C D n = sym (pentagon-p2 A B C D n) ∙ spoke-v2 A B C D n

  abstract
    spoke-v4 : ∀ A B C D n → cauchy R A (cauchy R B (cauchy R C D)) n ≡ tensor-int-4way A B C D n
    spoke-v4 A B C D n = sym (pentagon-p3 A B C D n) ∙ spoke-v3 A B C D n

  abstract
    spoke-v5 : ∀ A B C D n → cauchy R (cauchy R A B) (cauchy R C D) n ≡ tensor-int-4way A B C D n
    spoke-v5 A B C D n = sym (pentagon-q1 A B C D n) ∙ spoke-v1 A B C D n

  -- =======================================================================
  -- 📐 3. 5枚の三角形（完全隔離型 abstract・安全な初期化）
  -- =======================================================================
  abstract
    Triangle-1 : ∀ A B C D n → (pentagon-p1 A B C D n ∙ spoke-v2 A B C D n) ≡ spoke-v1 A B C D n
    Triangle-1 A B C D n = carrier-is-set 
      {x = cauchy R (cauchy R (cauchy R A B) C) D n} 
      {y = tensor-int-4way A B C D n}
      (pentagon-p1 A B C D n ∙ spoke-v2 A B C D n) 
      (spoke-v1 A B C D n)

  abstract
    Triangle-2 : ∀ A B C D n → (pentagon-p2 A B C D n ∙ spoke-v3 A B C D n) ≡ spoke-v2 A B C D n
    Triangle-2 A B C D n = 
      begin⇒
        (pentagon-p2 A B C D n) ∙ (sym (pentagon-p2 A B C D n) ∙ spoke-v2 A B C D n)
      ≡⟨ GL.assoc (pentagon-p2 A B C D n) (sym (pentagon-p2 A B C D n)) (spoke-v2 A B C D n) ⟩⇒
        ((pentagon-p2 A B C D n) ∙ sym (pentagon-p2 A B C D n)) ∙ spoke-v2 A B C D n
      ≡⟨ cong (_∙ spoke-v2 A B C D n) (GL.rCancel (pentagon-p2 A B C D n)) ⟩⇒
        refl ∙ spoke-v2 A B C D n
      ≡⟨ sym (GL.lUnit (spoke-v2 A B C D n)) ⟩⇒
        spoke-v2 A B C D n
      ∎⇒

  abstract
    Triangle-3 : ∀ A B C D n → (pentagon-p3 A B C D n ∙ spoke-v4 A B C D n) ≡ spoke-v3 A B C D n
    Triangle-3 A B C D n = 
      begin⇒
        (pentagon-p3 A B C D n) ∙ (sym (pentagon-p3 A B C D n) ∙ spoke-v3 A B C D n)
      ≡⟨ GL.assoc (pentagon-p3 A B C D n) (sym (pentagon-p3 A B C D n)) (spoke-v3 A B C D n) ⟩⇒
        ((pentagon-p3 A B C D n) ∙ sym (pentagon-p3 A B C D n)) ∙ spoke-v3 A B C D n
      ≡⟨ cong (_∙ spoke-v3 A B C D n) (GL.rCancel (pentagon-p3 A B C D n)) ⟩⇒
        refl ∙ spoke-v3 A B C D n
      ≡⟨ sym (GL.lUnit (spoke-v3 A B C D n)) ⟩⇒
        spoke-v3 A B C D n
      ∎⇒

  abstract
    Triangle-4 : ∀ A B C D n → (pentagon-q1 A B C D n ∙ spoke-v5 A B C D n) ≡ spoke-v1 A B C D n
    Triangle-4 A B C D n = 
      begin⇒
        (pentagon-q1 A B C D n) ∙ (sym (pentagon-q1 A B C D n) ∙ spoke-v1 A B C D n)
      ≡⟨ GL.assoc (pentagon-q1 A B C D n) (sym (pentagon-q1 A B C D n)) (spoke-v1 A B C D n) ⟩⇒
        ((pentagon-q1 A B C D n) ∙ sym (pentagon-q1 A B C D n)) ∙ spoke-v1 A B C D n
      ≡⟨ cong (_∙ spoke-v1 A B C D n) (GL.rCancel (pentagon-q1 A B C D n)) ⟩⇒
        refl ∙ spoke-v1 A B C D n
      ≡⟨ sym (GL.lUnit (spoke-v1 A B C D n)) ⟩⇒
        spoke-v1 A B C D n
      ∎⇒

  abstract
    -- 💡 こちらも同様に _ _ を削除
    Triangle-5 : ∀ A B C D n → (pentagon-q2 A B C D n ∙ spoke-v4 A B C D n) ≡ spoke-v5 A B C D n
    Triangle-5 A B C D n = carrier-is-set (pentagon-q2 A B C D n ∙ spoke-v4 A B C D n) (spoke-v5 A B C D n)

  -- =======================================================================
  -- 🤐 4. 全自動等式ジッパー（完全独立・自作rUnitによる最強安定版！！）
  -- =======================================================================
  private
    -- 💡 秘密兵器1：Agda標準の rUnit は型の向きが逆だったり推論が迷子になるため、
    -- 「絶対に迷わない自作の rUnit（q ∙ refl ≡ q）」を定義します！
    my-rUnit : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → p ∙ refl ≡ p
    my-rUnit {x = x} p i j = 
      hcomp (λ k → λ {
          (i = i1) → p j
        ; (j = i0) → x
        ; (j = i1) → p i1
        }) (p j)

    -- 💡 秘密兵器2：自作 rUnit と J を組み合わせた、最強のキャンセル補題！
    -- これでAgda先生は一切の展開（eval）を諦め、ノーパスで通してくれます。
    cancel-right-path : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p q : x ≡ y) (r : y ≡ z) →
      (p ∙ r ≡ q ∙ r) → p ≡ q
    cancel-right-path p q r eq =
      let
        eq-refl : p ∙ refl ≡ q ∙ refl
        eq-refl = J (λ z' r' → (p ∙ r' ≡ q ∙ r') → p ∙ refl ≡ q ∙ refl) (λ e → e) r eq
      in
      sym (my-rUnit p) ∙ (eq-refl ∙ my-rUnit q)

  -- =======================================================================
  -- 🏁 5. 最終統合：エンジン冷却・メタ変数消滅版
  -- =======================================================================

  -- 💡 型定義を極限までシンプルにする（計算コストの固定）
  PentagonType : (A B C D : FormalPowerSeries R) (n : ℕ) → Type ℓ
  PentagonType A B C D n = 
    ((pentagon-p1 A B C D n ∙ pentagon-p2 A B C D n) ∙ pentagon-p3 A B C D n) 
    ≡ (pentagon-q1 A B C D n ∙ pentagon-q2 A B C D n)

  abstract
    -- 💡 盾（carrier-is-set）に、比較したいパスを「具体的」に教える
    pentagon-impl-complete : ∀ A B C D n → PentagonType A B C D n
    pentagon-impl-complete A B C D n = 
      carrier-is-set 
        ((pentagon-p1 A B C D n ∙ pentagon-p2 A B C D n) ∙ pentagon-p3 A B C D n) 
        (pentagon-q1 A B C D n ∙ pentagon-q2 A B C D n)

  -- 🏆 五角形図式の「完成品」
  -- インスタンス登録の直前に、全対象 A B C D に対して funExt を適用
  pentagon-final : ∀ A B C D → 
    (λ n → ((pentagon-p1 A B C D n ∙ pentagon-p2 A B C D n) ∙ pentagon-p3 A B C D n)) ≡ 
    (λ n → (pentagon-q1 A B C D n ∙ pentagon-q2 A B C D n))
  pentagon-final A B C D = funExt (λ n → pentagon-impl-complete A B C D n)

  ------------------------------------------------------------------------
  -- 弱モノイド圏のインスタンス
  ------------------------------------------------------------------------
  FPS-MonoidalCat : WeakMonoidalCategory {ℓobj = ℓ} {ℓhom = ℓ}
  FPS-MonoidalCat = record
    { Obj       = FormalPowerSeries R
    ; Hom       = λ A B → ∀ n → A n ≡ B n
    ; id        = λ n → refl
    ; _∘_       = λ f g n → g n ∙ f n
    ; assoc     = λ f g h → funExt λ n → sym (GL.assoc (h n) (g n) (f n))
    ; id-left   = λ f → funExt λ n → sym (GL.rUnit (f n))
    ; id-right  = λ f → funExt λ n → sym (GL.lUnit (f n))
    ; _⊗_       = cauchy R
    ; tensorHom = tensorHom-impl
    ; tensor-id   = tensor-id-impl
    ; tensor-comp = tensor-comp-impl
    ; Φ         = λ A B C n i → cauchy-assoc A B C i n
    ; Φ⁻¹       = λ A B C n i → sym (λ j → cauchy-assoc A B C j n) i
    ; Φ-inv-right = λ A B C → funExt λ n → GL.lCancel (λ i → cauchy-assoc A B C i n)
    ; Φ-inv-left  = λ A B C → funExt λ n → GL.rCancel (λ i → cauchy-assoc A B C i n)
    ; Φ-natural = Φ-natural-impl
    -- 💡 完成した「五角形の盾」をここにセット！
    ; pentagon  = pentagon-final 
    }