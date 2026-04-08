{-# OPTIONS --safe --cubical --guardedness #-}

module UMIN.L03_Func.KMS.UMIN_TheoremB_Sublimated where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
open import Cubical.Data.Int using (ℤ; pos; negsuc)
open import Cubical.Data.Nat using (ℕ; zero; suc)

-- ================================================================
-- 1. TFDSpace
-- ================================================================
record TFDSpace (A : Type₀) : Type₁ where
  field
    Jᵀ : A ≃ A
    Jᵀ-involutive : (a : A) → equivFun Jᵀ (equivFun Jᵀ a) ≡ a
    θ : A ≃ A
    tomita-takesaki : (a : A) → equivFun Jᵀ (equivFun θ (equivFun Jᵀ a)) ≡ equivFun (invEquiv θ) a

-- ================================================================
-- 2. Iterated equivalence + helpers
-- ================================================================
iter-equiv-pos : {A : Type₀} → ℕ → (A ≃ A) → (A ≃ A)
iter-equiv-pos zero    eq = idEquiv _
iter-equiv-pos (suc n) eq = compEquiv (iter-equiv-pos n eq) eq

iter-equiv : {A : Type₀} → ℤ → (A ≃ A) → (A ≃ A)
iter-equiv (pos n)    eq = iter-equiv-pos n eq
iter-equiv (negsuc n) eq = iter-equiv-pos (suc n) (invEquiv eq)

neg : ℤ → ℤ
neg (pos zero)    = pos zero
neg (pos (suc n)) = negsuc n
neg (negsuc n)    = pos (suc n)

-- ================================================================
-- KMS-Flow の前提（postulate の代わり：具体モデルまたは別モジュールで証明を与える）
-- ================================================================
record KMSFlowLaws {A : Type₀} (tfd : TFDSpace A) : Type₁ where
  open TFDSpace tfd
  private
    σ : ℤ → A ≃ A
    σ β = iter-equiv β θ
  field
    σ-neg-σ-pointwise : (β : ℤ) (x : A) → equivFun (σ (neg β)) (equivFun (σ β) x) ≡ x
    σ-σ-neg-pointwise : (β : ℤ) (x : A) → equivFun (σ β) (equivFun (σ (neg β)) x) ≡ x
    σ-kms-balance-sec :
      (β : ℤ) (a b : A) (q : b ≡ equivFun (σ (neg β)) a) →
      sym (σ-neg-σ-pointwise β b) ∙ cong (equivFun (σ (neg β))) (sym (sym (σ-σ-neg-pointwise β a) ∙ sym (cong (equivFun (σ β)) q)))
      ≡ q
    σ-kms-balance-ret :
      (β : ℤ) (a b : A) (p : a ≡ equivFun (σ β) b) →
      sym (σ-σ-neg-pointwise β a) ∙ sym (cong (equivFun (σ β)) (sym (σ-neg-σ-pointwise β b) ∙ cong (equivFun (σ (neg β))) (sym p)))
      ≡ p

-- ================================================================
-- 3. KMS-Flow（σ の ℤ-群律は KMSFlowLaws で与える）
-- ================================================================
module KMS-Flow {A : Type₀} (tfd : TFDSpace A) (laws : KMSFlowLaws tfd) where
  open TFDSpace tfd
  open KMSFlowLaws laws

  σ : ℤ → A ≃ A
  σ β = iter-equiv β θ

  σ-zero : σ (pos 0) ≡ idEquiv A
  σ-zero = refl

  private

    -- IH から σₙ(Jᵀ x) ≡ Jᵀ(σ₋ₙ x)（両側に Jᵀ をかけて Jᵀ-involutive）
    σ-pos-Jᵀ-swap :
      (n : ℕ) (x : A) →
      equivFun Jᵀ (equivFun (σ (pos n)) (equivFun Jᵀ x)) ≡ equivFun (σ (neg (pos n))) x →
      equivFun (σ (pos n)) (equivFun Jᵀ x) ≡ equivFun Jᵀ (equivFun (σ (neg (pos n))) x)
    σ-pos-Jᵀ-swap n x ih =
      sym (Jᵀ-involutive (equivFun (σ (pos n)) (equivFun Jᵀ x))) ∙ cong (equivFun Jᵀ) ih

    -- Tomita–Takesaki を a = σ₋ₙ(x) に適用し、左を IH＋swap で整える
    TT-step-pos-suc :
      (n : ℕ) (x : A) →
      equivFun Jᵀ (equivFun (σ (pos n)) (equivFun Jᵀ x)) ≡ equivFun (σ (neg (pos n))) x →
      equivFun Jᵀ (equivFun θ (equivFun (σ (pos n)) (equivFun Jᵀ x)))
      ≡ equivFun (invEquiv θ) (equivFun (σ (neg (pos n))) x)
    TT-step-pos-suc n x ih =
      equivFun Jᵀ (equivFun θ (equivFun (σ (pos n)) (equivFun Jᵀ x)))
        ≡⟨ cong (λ z → equivFun Jᵀ (equivFun θ z)) (σ-pos-Jᵀ-swap n x ih) ⟩
      equivFun Jᵀ (equivFun θ (equivFun Jᵀ (equivFun (σ (neg (pos n))) x)))
        ≡⟨ tomita-takesaki (equivFun (σ (neg (pos n))) x) ⟩
      equivFun (invEquiv θ) (equivFun (σ (neg (pos n))) x) ∎

    -- inv(θ) ∘ σ(−(pos n)) = σ(negsuc n)（ℤ の字下げと compEquiv の定義）
    σ-inv-θ-step : (n : ℕ) (x : A) →
      equivFun (invEquiv θ) (equivFun (σ (neg (pos n))) x) ≡ equivFun (σ (negsuc n)) x
    σ-inv-θ-step zero x =
      equivFun (invEquiv θ) (equivFun (σ (pos zero)) x) ≡⟨ cong (λ h → equivFun (invEquiv θ) (equivFun h x)) σ-zero ⟩
      equivFun (invEquiv θ) x ≡⟨ refl ⟩
      equivFun (compEquiv (idEquiv A) (invEquiv θ)) x ≡⟨ refl ⟩
      equivFun (σ (negsuc zero)) x ∎
    σ-inv-θ-step (suc n) x =
      equivFun (invEquiv θ) (equivFun (σ (negsuc n)) x) ≡⟨ refl ⟩
      equivFun (compEquiv (σ (negsuc n)) (invEquiv θ)) x ≡⟨ refl ⟩
      equivFun (σ (negsuc (suc n))) x ∎

    -- θ = inv(θ) を Jᵀ で共役（tomita-takesaki を invEquiv θ に対して使うのと同型）
    TT-J-inv-θ : (x : A) →
      equivFun Jᵀ (equivFun (invEquiv θ) (equivFun Jᵀ x)) ≡ equivFun θ x
    TT-J-inv-θ x =
      equivFun Jᵀ (equivFun (invEquiv θ) (equivFun Jᵀ x))
        ≡⟨ cong (equivFun Jᵀ)
             (sym (sym (cong (λ z → equivFun Jᵀ (equivFun θ z)) (Jᵀ-involutive x)) ∙ tomita-takesaki (equivFun Jᵀ x)))
          ∙ Jᵀ-involutive (equivFun θ x) ⟩
      equivFun θ x ∎

    -- y に対して Jᵀ(inv θ y) ≡ θ(Jᵀ y)（上で x = Jᵀ y とおいたものを y で書き直す）
    TT-J-inv-on-y : (y : A) →
      equivFun Jᵀ (equivFun (invEquiv θ) y) ≡ equivFun θ (equivFun Jᵀ y)
    TT-J-inv-on-y y =
      equivFun Jᵀ (equivFun (invEquiv θ) y)
        ≡⟨ sym (cong (equivFun Jᵀ ∘ equivFun (invEquiv θ)) (Jᵀ-involutive y)) ⟩
      equivFun Jᵀ (equivFun (invEquiv θ) (equivFun Jᵀ (equivFun Jᵀ y)))
        ≡⟨ TT-J-inv-θ (equivFun Jᵀ y) ⟩
      equivFun θ (equivFun Jᵀ y) ∎

  -- generalized Tomita-Takesaki（帰納的に証明）
  generalized-tt : (β : ℤ) (x : A) →
    equivFun Jᵀ (equivFun (σ β) (equivFun Jᵀ x)) ≡ equivFun (σ (neg β)) x
  generalized-tt (pos zero)    x = Jᵀ-involutive x  -- β=0 の場合
  generalized-tt (pos (suc n)) x =
    let ih = generalized-tt (pos n) x in
    equivFun Jᵀ (equivFun (σ (pos (suc n))) (equivFun Jᵀ x))
      ≡⟨ refl ⟩
    equivFun Jᵀ (equivFun θ (equivFun (σ (pos n)) (equivFun Jᵀ x)))
      ≡⟨ TT-step-pos-suc n x ih ⟩
    equivFun (invEquiv θ) (equivFun (σ (neg (pos n))) x)
      ≡⟨ σ-inv-θ-step n x ⟩
    equivFun (σ (negsuc n)) x
      ≡⟨ refl ⟩
    equivFun (σ (neg (pos (suc n)))) x ∎
  generalized-tt (negsuc zero) x =
    equivFun Jᵀ (equivFun (σ (negsuc zero)) (equivFun Jᵀ x))
      ≡⟨ refl ⟩
    equivFun Jᵀ (equivFun (invEquiv θ) (equivFun Jᵀ x))
      ≡⟨ TT-J-inv-θ x ⟩
    equivFun θ x
      ≡⟨ refl ⟩
    equivFun (σ (pos (suc zero))) x
      ≡⟨ refl ⟩
    equivFun (σ (neg (negsuc zero))) x ∎
  generalized-tt (negsuc (suc n)) x =
    let y = equivFun (σ (negsuc n)) (equivFun Jᵀ x) in
    equivFun Jᵀ (equivFun (σ (negsuc (suc n))) (equivFun Jᵀ x))
      ≡⟨ refl ⟩
    equivFun Jᵀ (equivFun (invEquiv θ) y)
      ≡⟨ TT-J-inv-on-y y ⟩
    equivFun θ (equivFun Jᵀ y)
      ≡⟨ cong (equivFun θ) (generalized-tt (negsuc n) x) ⟩
    equivFun θ (equivFun (σ (pos (suc n))) x)
      ≡⟨ refl ⟩
    equivFun (σ (pos (suc (suc n)))) x
      ≡⟨ refl ⟩
    equivFun (σ (neg (negsuc (suc n)))) x ∎

  -- KMS詳細バランス（あなたの提案を維持）
  kms-balance : (β : ℤ) (a b : A) →
    (a ≡ equivFun (σ β) b) ≃ (b ≡ equivFun (σ (neg β)) a)
  kms-balance β a b = isoToEquiv the-iso
    where
      the-iso : Iso (a ≡ equivFun (σ β) b) (b ≡ equivFun (σ (neg β)) a)
      the-iso .Iso.fun p =
        sym (σ-neg-σ-pointwise β b) ∙ cong (equivFun (σ (neg β))) (sym p)
      the-iso .Iso.inv q =
        sym (σ-σ-neg-pointwise β a) ∙ sym (cong (equivFun (σ β)) q)

      the-iso .Iso.sec = σ-kms-balance-sec β a b
      the-iso .Iso.ret = σ-kms-balance-ret β a b

-- ================================================================
-- 4. SasakiTFD-Bridge（J / ortho-duality / defect-duality）
-- ================================================================
-- θ = s ∘ s† = compEquiv s† s。defect-duality は ortho 鎖の終項 s†(s(a)) と inv(θ)(a) を一致させる。
prove-tomita-takesaki-from :
  {A : Type₀} (s s† Jᵀ : A ≃ A) →
  (Jᵀ-involutive : (a : A) → equivFun Jᵀ (equivFun Jᵀ a) ≡ a) →
  (ortho-duality-s : (a : A) → equivFun Jᵀ (equivFun s (equivFun Jᵀ a)) ≡ equivFun s† a) →
  (ortho-duality-s† : (a : A) → equivFun Jᵀ (equivFun s† (equivFun Jᵀ a)) ≡ equivFun s a) →
  (defect-duality :
     (a : A) →
     equivFun s† (equivFun s a) ≡ equivFun (invEquiv (compEquiv s† s)) a) →
  (a : A) →
  equivFun Jᵀ (equivFun (compEquiv s† s) (equivFun Jᵀ a)) ≡ equivFun (invEquiv (compEquiv s† s)) a
prove-tomita-takesaki-from s s† Jᵀ Jᵀ-involutive ortho-duality-s ortho-duality-s† defect-duality a =
  equivFun Jᵀ (equivFun s (equivFun s† (equivFun Jᵀ a)))
    ≡⟨ cong (equivFun Jᵀ ∘ equivFun s) (sym (Jᵀ-involutive (equivFun s† (equivFun Jᵀ a)))) ⟩
  equivFun Jᵀ (equivFun s (equivFun Jᵀ (equivFun Jᵀ (equivFun s† (equivFun Jᵀ a)))))
    ≡⟨ cong (λ x → equivFun Jᵀ (equivFun s (equivFun Jᵀ x))) (ortho-duality-s† a) ⟩
  equivFun Jᵀ (equivFun s (equivFun Jᵀ (equivFun s a)))
    ≡⟨ ortho-duality-s (equivFun s a) ⟩
  equivFun s† (equivFun s a)
    ≡⟨ defect-duality a ⟩
  equivFun (invEquiv (compEquiv s† s)) a ∎

record SasakiTFD-Bridge (A : Type₀) : Type₁ where
  field
    s : A ≃ A
    s† : A ≃ A
    Jᵀ : A ≃ A
    Jᵀ-involutive : (a : A) → equivFun Jᵀ (equivFun Jᵀ a) ≡ a
    ortho-duality-s  : (a : A) → equivFun Jᵀ (equivFun s (equivFun Jᵀ a)) ≡ equivFun s† a
    ortho-duality-s† : (a : A) → equivFun Jᵀ (equivFun s† (equivFun Jᵀ a)) ≡ equivFun s a
    defect-duality :
      (a : A) →
      equivFun s† (equivFun s a) ≡ equivFun (invEquiv (compEquiv s† s)) a
    kms-flow-laws :
      KMSFlowLaws
        (record
          { Jᵀ             = Jᵀ
          ; Jᵀ-involutive  = Jᵀ-involutive
          ; θ              = compEquiv s† s
          ; tomita-takesaki =
              λ a → prove-tomita-takesaki-from s s† Jᵀ Jᵀ-involutive ortho-duality-s ortho-duality-s† defect-duality a
          })

module Extract-TFD {A : Type₀} (bridge : SasakiTFD-Bridge A) where
  open SasakiTFD-Bridge bridge

  extract-J : A ≃ A
  extract-J = Jᵀ

  extract-θ : A ≃ A
  extract-θ = compEquiv s† s

  prove-tomita-takesaki : (a : A) →
    equivFun extract-J (equivFun extract-θ (equivFun extract-J a)) ≡ equivFun (invEquiv extract-θ) a
  prove-tomita-takesaki a =
    prove-tomita-takesaki-from s s† Jᵀ Jᵀ-involutive ortho-duality-s ortho-duality-s† defect-duality a

  theorem-B-tfd : TFDSpace A
  theorem-B-tfd = record
    { Jᵀ             = extract-J
    ; Jᵀ-involutive  = Jᵀ-involutive
    ; θ              = extract-θ
    ; tomita-takesaki = prove-tomita-takesaki
    }

  laws = kms-flow-laws

  open KMS-Flow theorem-B-tfd laws public