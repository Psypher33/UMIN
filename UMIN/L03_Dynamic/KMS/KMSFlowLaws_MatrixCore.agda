{-# OPTIONS --safe --cubical --guardedness #-}

------------------------------------------------------------------------
-- Task 0-3: KMSFlowLaws の具体キャリア（M_n の計算可能コア）
--
-- 複素数をガウス有理数 ℚ×ℚ で表し、Cubical の FinMatrix で M_n を表現する。
-- Jᵀ = θ = idEquiv の自明なモジュラー流を載せ、KMSFlowLaws を isSet 上で閉じる。
-- （本格的な随伴・Tomita 演算子は同一 isSet キャリア上の別等価に差し替え可能。）
------------------------------------------------------------------------

module UMIN.L03_Dynamic.KMS.KMSFlowLaws_MatrixCore where

open import Agda.Primitive using (lzero)
open import Cubical.Foundations.Prelude
  using ( Type; _≡_; refl; sym; _∙_; cong; isProp; isSet; isProp→PathP )
open import Cubical.Foundations.HLevels using (isSetΠ2; isSet×)
open import Cubical.Foundations.Equiv
  using (_≃_; equivFun; invEquiv; compEquiv; idEquiv; invEquivIdEquiv)

open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Int using (ℤ; pos; negsuc)
open import Cubical.Algebra.Matrix using (FinMatrix)

open import Cubical.Data.Rationals.MoreRationals.QuoQ using (ℚ; isSetℚ)

open import UMIN.L02_Obstruction.Pi1.UMIN_TheoremB_Sublimated
  using ( TFDSpace; KMSFlowLaws; iter-equiv; iter-equiv-pos; neg )

------------------------------------------------------------------------
-- ガウス有理数 · M_n
------------------------------------------------------------------------

Complexℚ : Type lzero
Complexℚ = ℚ × ℚ

isSetComplexℚ : isSet Complexℚ
isSetComplexℚ = isSet× isSetℚ isSetℚ

Mn : ℕ → Type lzero
Mn n = FinMatrix Complexℚ n n

isSetMn : (n : ℕ) → isSet (Mn n)
isSetMn n = isSetΠ2 λ _ _ → isSetComplexℚ

------------------------------------------------------------------------
-- θ = id のとき、iter-equiv は各点で恒等（KMS 法則の簡約に使う）
------------------------------------------------------------------------

private
  equivFun-id : {A : Type lzero} (x : A) → equivFun (idEquiv A) x ≡ x
  equivFun-id x = refl

  -- compEquiv f g の実装は g ∘ f（Cubical/Foundations/Equiv.agda）
  equivFun-compRev :
    {A B C : Type lzero} (f : A ≃ B) (g : B ≃ C) (x : A)
    → equivFun (compEquiv f g) x ≡ equivFun g (equivFun f x)
  equivFun-compRev f g x = refl

  invEquiv-idEquiv : ∀ {A : Type lzero} → invEquiv (idEquiv A) ≡ idEquiv A
  invEquiv-idEquiv {A} = invEquivIdEquiv A

  equivFun-iter-equiv-pos-id :
    {A : Type lzero} (n : ℕ) (x : A)
    → equivFun (iter-equiv-pos n (idEquiv A)) x ≡ x
  equivFun-iter-equiv-pos-id {A} zero x =
    equivFun-id x
  equivFun-iter-equiv-pos-id {A} (suc n) x =
    equivFun-compRev (iter-equiv-pos n (idEquiv A)) (idEquiv A) x
    ∙ equivFun-id (equivFun (iter-equiv-pos n (idEquiv A)) x)
    ∙ equivFun-iter-equiv-pos-id n x

  equivFun-iter-equiv-id :
    {A : Type lzero} (β : ℤ) (x : A)
    → equivFun (iter-equiv β (idEquiv A)) x ≡ x
  equivFun-iter-equiv-id {A} (pos n) x =
    equivFun-iter-equiv-pos-id n x
  equivFun-iter-equiv-id {A} (negsuc n) x =
    cong (λ e → equivFun (iter-equiv-pos (suc n) e) x) (invEquiv-idEquiv {A})
    ∙ equivFun-iter-equiv-pos-id (suc n) x

------------------------------------------------------------------------
-- 自明 TFD + KMSFlowLaws（Mn n 上）
------------------------------------------------------------------------

module MnKMS (n : ℕ) where

  private
    A = Mn n

  tfd-trivial : TFDSpace A
  tfd-trivial = record
    { Jᵀ             = idEquiv A
    ; Jᵀ-involutive  = λ _ → refl
    ; θ              = idEquiv A
    ; tomita-takesaki = λ _ → refl
    }

  private
    σ : ℤ → A ≃ A
    σ β = iter-equiv β (idEquiv A)

    σ-neg-σ : (β : ℤ) (x : A) → equivFun (σ (neg β)) (equivFun (σ β) x) ≡ x
    σ-neg-σ β x =
      cong (equivFun (σ (neg β))) (equivFun-iter-equiv-id β x)
      ∙ equivFun-iter-equiv-id (neg β) x

    σ-σ-neg : (β : ℤ) (x : A) → equivFun (σ β) (equivFun (σ (neg β)) x) ≡ x
    σ-σ-neg β x =
      cong (equivFun (σ β)) (equivFun-iter-equiv-id (neg β) x)
      ∙ equivFun-iter-equiv-id β x

  kms-laws-trivial : KMSFlowLaws tfd-trivial
  kms-laws-trivial = record
    { σ-neg-σ-pointwise = σ-neg-σ
    ; σ-σ-neg-pointwise = σ-σ-neg
    ; σ-kms-balance-sec = λ β a b q →
        isProp→PathP (λ _ → isSetMn n b (equivFun (σ (neg β)) a)) _ _
    ; σ-kms-balance-ret = λ β a b p →
        isProp→PathP (λ _ → isSetMn n a (equivFun (σ β) b)) _ _
    }

open MnKMS public using (tfd-trivial; kms-laws-trivial)
