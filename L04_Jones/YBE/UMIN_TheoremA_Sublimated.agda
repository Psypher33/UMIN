{-# OPTIONS --cubical --guardedness --safe --lossy-unification #-}

module UMIN.L04_Jones.YBE.UMIN_TheoremA_Sublimated where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (isoToEquiv; iso)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Int using (ℤ; pos; negsuc; _+_; -_)
open import Cubical.Data.Int.Properties using (+Assoc; +Comm; -Cancel'; -Dist+; pos0+)

open import Cubical.Algebra.SymmetricGroup using (SymGroup)
open import Cubical.Algebra.Group.ZAction using (distrℤ·; _ℤ[_]·_)

open import UMIN.L02_Obstruction.Pi1.UMIN_TheoremB_Sublimated

-- ================================================================
-- 1. Thermal R-Matrix（Equiv版に強化）
-- ================================================================
module ThermalYBE {A : Type₀} (isA : isSet A) (tfd : TFDSpace A) (laws : KMSFlowLaws tfd) where
  open TFDSpace tfd
  open KMSFlowLaws laws
  open KMS-Flow tfd laws

  -- KMS 側の neg と Cubical の - を同一視（証明は構造が同じなので refl）
  negEqCubical : (x : ℤ) → neg x ≡ - x
  negEqCubical (pos zero) = refl
  negEqCubical (pos (suc n)) = refl
  negEqCubical (negsuc n) = refl

  negDistPlus : (m n : ℤ) → neg (m + n) ≡ neg m + neg n
  negDistPlus m n =
      negEqCubical (m + n)
    ∙ -Dist+ m n
    ∙ sym (cong₂ _+_ (negEqCubical m) (negEqCubical n))

  private
    G = SymGroup A isA

  -- compEquiv f g は g∘f なので、正の冪では「θ を左に回す」定義と iter-equiv の順序が違う。
  -- 点ごとに θ(σⁿx) ≡ σⁿ(θx) を示し、equivEq funExt で Equiv の等式にする。
  swapθ-pos : (n : ℕ) (x : A) →
    equivFun (compEquiv (σ (pos n)) θ) x ≡ equivFun (compEquiv θ (σ (pos n))) x
  swapθ-pos zero x = refl
  swapθ-pos (suc n) x = cong (equivFun θ) (swapθ-pos n x)

  swapθ-pos-equiv : (n : ℕ) → compEquiv (σ (pos n)) θ ≡ compEquiv θ (σ (pos n))
  swapθ-pos-equiv n = equivEq (funExt (swapθ-pos n))

  swapθ-negsuc : (n : ℕ) (x : A) →
    equivFun (compEquiv (σ (negsuc n)) (invEquiv θ)) x ≡
    equivFun (compEquiv (invEquiv θ) (σ (negsuc n))) x
  swapθ-negsuc zero x = refl
  swapθ-negsuc (suc n) x = cong (equivFun (invEquiv θ)) (swapθ-negsuc n x)

  swapθ-negsuc-equiv : (n : ℕ) → compEquiv (σ (negsuc n)) (invEquiv θ) ≡ compEquiv (invEquiv θ) (σ (negsuc n))
  swapθ-negsuc-equiv n = equivEq (funExt (swapθ-negsuc n))

  -- σ z は ℤ が生成する θ 上の作用（SymGroup）と一致する
  sigmaEqZAction : (z : ℤ) → σ z ≡ z ℤ[ G ]· θ
  sigmaEqZAction (pos zero) = refl
  sigmaEqZAction (pos (suc n)) =
      σ (pos (suc n)) ≡⟨ refl ⟩
      compEquiv (σ (pos n)) θ
        ≡⟨ swapθ-pos-equiv n ∙ cong (λ e → compEquiv θ e) (sigmaEqZAction (pos n)) ⟩
      compEquiv θ (pos n ℤ[ G ]· θ) ≡⟨ refl ⟩
      pos (suc n) ℤ[ G ]· θ ∎
  sigmaEqZAction (negsuc zero) =
    σ (negsuc zero) ≡⟨ refl ⟩
    compEquiv (idEquiv A) (invEquiv θ) ≡⟨ compEquivIdEquiv (invEquiv θ) ⟩
    invEquiv θ ≡⟨ refl ⟩
    negsuc zero ℤ[ G ]· θ ∎
  sigmaEqZAction (negsuc (suc n)) =
      σ (negsuc (suc n)) ≡⟨ refl ⟩
      compEquiv (σ (negsuc n)) (invEquiv θ)
        ≡⟨ swapθ-negsuc-equiv n ∙ cong (λ e → compEquiv (invEquiv θ) e) (sigmaEqZAction (negsuc n)) ⟩
      compEquiv (invEquiv θ) (negsuc n ℤ[ G ]· θ) ≡⟨ refl ⟩
      negsuc (suc n) ℤ[ G ]· θ ∎

  -- σ が群準同型（compEquiv）であること：ZAction.distrℤ· と sigmaEqZAction から
  sigmaCompEquiv : (α β : ℤ) → σ (α + β) ≡ compEquiv (σ β) (σ α)
  sigmaCompEquiv α β =
      cong σ (+Comm α β)
    ∙ sigmaEqZAction (β + α)
    ∙ distrℤ· G θ β α
    ∙ cong₂ compEquiv (sym (sigmaEqZAction β)) (sym (sigmaEqZAction α))

  sigmaAdditivity : (α β : ℤ) (x : A) →
    equivFun (σ α) (equivFun (σ β) x) ≡ equivFun (σ (α + β)) x
  sigmaAdditivity α β x = cong (λ e → equivFun e x) (sym (sigmaCompEquiv α β))

  -- Thermal R-matrix を Equiv として定義（YBE証明がやりやすい）
  -- fun = inv だが、2 回適用で id になることは KMS の σ/σ⁻¹ 関係で示す（refl ではない）
  Thermal-R₁₂ : ℤ → (A × A × A) ≃ (A × A × A)
  Thermal-R₁₂ β = isoToEquiv (iso fun inv sec ret)
    where
      fun : A × A × A → A × A × A
      fun (v₁ , v₂ , v₃) = (equivFun (σ β) v₂ , equivFun (σ (neg β)) v₁ , v₃)

      inv : A × A × A → A × A × A
      inv (v₁ , v₂ , v₃) = (equivFun (σ β) v₂ , equivFun (σ (neg β)) v₁ , v₃)

      sec : ∀ b → fun (inv b) ≡ b
      sec (v₁ , v₂ , v₃) =
        ΣPathP (σ-σ-neg-pointwise β v₁ , ΣPathP (σ-neg-σ-pointwise β v₂ , refl))

      ret : ∀ a → inv (fun a) ≡ a
      ret = sec

  Thermal-R₁₃ : ℤ → (A × A × A) ≃ (A × A × A)
  Thermal-R₁₃ δ = isoToEquiv (iso fun inv sec ret)
    where
      fun : A × A × A → A × A × A
      fun (v₁ , v₂ , v₃) = (equivFun (σ δ) v₃ , v₂ , equivFun (σ (neg δ)) v₁)

      inv : A × A × A → A × A × A
      inv (v₁ , v₂ , v₃) = (equivFun (σ δ) v₃ , v₂ , equivFun (σ (neg δ)) v₁)

      sec : ∀ b → fun (inv b) ≡ b
      sec (v₁ , v₂ , v₃) =
        ΣPathP (σ-σ-neg-pointwise δ v₁ , ΣPathP (refl , σ-neg-σ-pointwise δ v₃))

      ret : ∀ a → inv (fun a) ≡ a
      ret = sec

  Thermal-R₂₃ : ℤ → (A × A × A) ≃ (A × A × A)
  Thermal-R₂₃ δ = isoToEquiv (iso fun inv sec ret)
    where
      fun : A × A × A → A × A × A
      fun (v₁ , v₂ , v₃) = (v₁ , equivFun (σ δ) v₃ , equivFun (σ (neg δ)) v₂)

      inv : A × A × A → A × A × A
      inv (v₁ , v₂ , v₃) = (v₁ , equivFun (σ δ) v₃ , equivFun (σ (neg δ)) v₂)

      sec : ∀ b → fun (inv b) ≡ b
      sec (v₁ , v₂ , v₃) =
        ΣPathP (refl , ΣPathP (σ-σ-neg-pointwise δ v₂ , σ-neg-σ-pointwise δ v₃))

      ret : ∀ a → inv (fun a) ≡ a
      ret = sec

  -- ================================================================
  -- 2. 熱的 Yang-Baxter 方程式
  -- ================================================================
  module YBE-Components (β γ : ℤ) (v₁ v₂ v₃ : A) where

    gammaNegGamma0 : γ + (neg γ) ≡ pos zero
    gammaNegGamma0 =
      sym (+Comm (neg γ) γ) ∙ cong (_+ γ) (negEqCubical γ) ∙ -Cancel' γ

    -- 左辺成分1
    left1 = equivFun (σ β) (equivFun (σ γ) v₃)
    right1 = equivFun (σ (β + γ)) v₃
    part1 : left1 ≡ right1
    part1 = sigmaAdditivity β γ v₃

    -- 成分2（中）：両辺とも v₂ に退化（σ-加法性と σ₋β∘σβ = id）
    left2 =
      equivFun (σ (neg β)) (equivFun (σ (β + γ)) (equivFun (σ (neg γ)) v₂))
    right2 =
      equivFun (σ γ) (equivFun (σ (neg (β + γ))) (equivFun (σ β) v₂))

    betaGammaNegGamma : (β + γ) + (neg γ) ≡ β
    betaGammaNegGamma =
      (β + γ) + (neg γ) ≡⟨ sym (+Assoc β γ (neg γ)) ⟩
      β + (γ + (neg γ)) ≡⟨ cong (β +_) gammaNegGamma0 ⟩
      β + pos zero ≡⟨ refl ⟩
      β ∎

    negSumPlusBetaEqNegGamma : (neg (β + γ)) + β ≡ neg γ
    negSumPlusBetaEqNegGamma =
      (neg (β + γ)) + β ≡⟨ cong (_+ β) (negDistPlus β γ) ⟩
      ((neg β) + (neg γ)) + β ≡⟨ sym (+Assoc (neg β) (neg γ) β) ⟩
      (neg β) + ((neg γ) + β) ≡⟨ cong ((neg β) +_) (+Comm (neg γ) β) ⟩
      (neg β) + (β + (neg γ)) ≡⟨ +Assoc (neg β) β (neg γ) ⟩
      ((neg β) + β) + (neg γ) ≡⟨ cong (_+ (neg γ)) (cong (_+ β) (negEqCubical β) ∙ -Cancel' β) ⟩
      pos zero + (neg γ) ≡⟨ sym (pos0+ (neg γ)) ⟩
      neg γ ∎

    part2 : left2 ≡ right2
    part2 =
        cong (equivFun (σ (neg β)))
          (sigmaAdditivity (β + γ) (neg γ) v₂ ∙ cong (λ z → equivFun (σ z) v₂) betaGammaNegGamma)
      ∙ σ-neg-σ-pointwise β v₂
      ∙ sym
          ( cong (equivFun (σ γ))
              (sigmaAdditivity (neg (β + γ)) β v₂ ∙ cong (λ z → equivFun (σ z) v₂) negSumPlusBetaEqNegGamma)
          ∙ σ-σ-neg-pointwise γ v₂
          )

    -- 成分3： -Dist+ と σ の可換性（σα∘σβ = σβ∘σα）
    left3 = equivFun (σ (neg (β + γ))) v₁
    right3 = equivFun (σ (neg γ)) (equivFun (σ (neg β)) v₁)

    sigmaCommute : (α δ : ℤ) (x : A) →
      equivFun (σ α) (equivFun (σ δ) x) ≡ equivFun (σ δ) (equivFun (σ α) x)
    sigmaCommute α δ x =
        sigmaAdditivity α δ x
      ∙ cong (λ z → equivFun (σ z) x) (+Comm α δ)
      ∙ sym (sigmaAdditivity δ α x)

    part3 : left3 ≡ right3
    part3 =
        cong (λ z → equivFun (σ z) v₁) (negDistPlus β γ)
      ∙ sym (sigmaAdditivity (neg β) (neg γ) v₁)
      ∙ sigmaCommute (neg β) (neg γ) v₁

  -- まず、各点における作用の一致を示す（ホモトピー）
  thermal-YBE-pointwise : (β γ : ℤ) (v : A × A × A) →
    equivFun (Thermal-R₁₂ β) (equivFun (Thermal-R₁₃ (β + γ)) (equivFun (Thermal-R₂₃ γ) v))
    ≡
    equivFun (Thermal-R₂₃ γ) (equivFun (Thermal-R₁₃ (β + γ)) (equivFun (Thermal-R₁₂ β) v))
  thermal-YBE-pointwise β γ (v₁ , v₂ , v₃) =
    let open YBE-Components β γ v₁ v₂ v₃ in
    λ i → (part1 i , part2 i , part3 i)

  -- 関数外延性と equivEq で Equiv の等式に持ち上げる
  thermal-YBE : (β γ : ℤ) →
    compEquiv (Thermal-R₂₃ γ) (compEquiv (Thermal-R₁₃ (β + γ)) (Thermal-R₁₂ β))
    ≡
    compEquiv (Thermal-R₁₂ β) (compEquiv (Thermal-R₁₃ (β + γ)) (Thermal-R₂₃ γ))
  thermal-YBE β γ = equivEq (funExt (thermal-YBE-pointwise β γ))

-- ================================================================
-- 将来的な接続：TremblingCore / SasakiTFD-Bridge からインスタンス生成
-- ================================================================
-- module FromSasaki {A : Type₀} (isA : isSet A) (bridge : SasakiTFD-Bridge A) where
--   open Extract-TFD bridge
--   open ThermalYBE isA theorem-B-tfd kms-flow-laws-on-tfd