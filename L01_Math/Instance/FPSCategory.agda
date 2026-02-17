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

  -- 🔹 finiteSum-ext が pointwise ∙ を分配
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
    -- 🗡️ cauchy-assoc のパスが、3つのブロックの直列結合に等しいことを示す 2-path
    --     （assoc-distrib / assoc-proof / assoc-block3 は
    --       すでに CauchyAssoc.agda 内で定義済みのものをそのまま使う）
    assoc-distrib-path : ∀ (X Y Z : FormalPowerSeries R) →
      cauchy-assoc X Y Z ≡ (assoc-distrib X Y Z ∙ assoc-proof X Y Z ∙ assoc-block3 X Y Z)
    assoc-distrib-path X Y Z = refl

    -- 🗡️ 変化のワープ（Step 2用：次なる主戦場！）
    warp-double-sum : ∀ {A A' B B' C C' : FormalPowerSeries R}
      (f : ∀ n → A n ≡ A' n) (g : ∀ n → B n ≡ B' n) (h : ∀ n → C n ≡ C' n) n →
      (tensorHom-impl (tensorHom-impl f g) h n ∙ 
        (λ i → (assoc-distrib A' B' C' ∙ assoc-proof A' B' C' ∙ assoc-block3 A' B' C') i n)) ≡
      ((λ i → (assoc-distrib A B C ∙ assoc-proof A B C ∙ assoc-block3 A B C) i n) ∙ 
        tensorHom-impl f (tensorHom-impl g h) n)
    warp-double-sum f g h n = {!!}

  ------------------------------------------------------------------------
  -- Φ の自然性（アソシエータと tensorHom の可換性）
  ------------------------------------------------------------------------
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

  ------------------------------------------------------------------------
  -- WeakMonoidalCategory インスタンス
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
    ; pentagon  = {!!}
    }