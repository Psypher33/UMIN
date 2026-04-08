{-# OPTIONS --cubical --guardedness --safe --lossy-unification #-}

module UMIN.L03_Func.Topology.UMIN_ThermalBraid where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary.Base using (¬_; Dec; yes; no)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Data.Sigma using (_×_; ΣPathP)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (isoToEquiv; iso)
open import Cubical.Data.Vec using (Vec; _∷_; []; _++_; lookup; head; tail)
open import Cubical.Data.Vec.Properties using (FinVec→Vec; Vec→FinVec; Vec→FinVec→Vec; FinVec→Vec→FinVec)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Cubical.Data.Nat.Properties using (+-comm)
open import Cubical.Data.FinData.Base using (Fin; zero; suc; toℕ; weakenFin; ¬Fin0; FinVec)
open import Cubical.Data.FinData.Properties using (toℕ<n; weakenRespToℕ; discreteFin; injSucFin; znots)

open import Cubical.Data.Int using (ℤ)

open import UMIN.L03_Func.KMS.UMIN_TheoremB_Sublimated
open import UMIN.L03_Func.YBE.UMIN_TheoremA_Sublimated

-- ================================================================
-- 熱的ブレイド群（Thermal Braid Group）—— FinVec 観測版
-- ================================================================
module ThermalBraid (A : Type₀) (M : ℕ) (isA : isSet A) (tfd : TFDSpace A) (laws : KMSFlowLaws tfd) where
  N : ℕ
  N = suc M
  open ThermalYBE isA tfd laws
  open KMSFlowLaws laws
  open KMS-Flow tfd laws renaming (σ to σ-flow)

  private
    p0≢p1-aux : ∀ {m} (i : Fin m) → ¬ (weakenFin i ≡ suc i)
    p0≢p1-aux zero eq = znots eq
    p0≢p1-aux (suc i) eq = p0≢p1-aux i (injSucFin eq)

    p0≢p1 : ∀ (i : Fin (N ∸ 1)) → ¬ (weakenFin i ≡ suc i)
    p0≢p1 = p0≢p1-aux

    -- ★ 推論迷子を防ぐ唯一の道標（不可能ルートのパスの型を明示）
    absurd-eqA : ∀ {x y : A} → ⊥ → x ≡ y
    absurd-eqA ()

  -- 1. 基本2本糸熱的交差
  Thermal-R2 : ℤ → (A × A) ≃ (A × A)
  Thermal-R2 β = isoToEquiv (iso fun inv sec ret)
    where
      fun inv : A × A → A × A
      fun (v₁ , v₂) = (equivFun (σ-flow β) v₂ , equivFun (σ-flow (neg β)) v₁)
      inv = fun
      sec ret : ∀ b → fun (inv b) ≡ b
      sec (v₁ , v₂) i = (σ-σ-neg-pointwise β v₁ i , σ-neg-σ-pointwise β v₂ i)
      ret = sec

  -- 2. 熱的ブレイド生成元 σ_i^β (FinVec 局所観測アプローチ)
  σ : (i : Fin (N ∸ 1)) (β : ℤ) → (Vec A N ≃ Vec A N)
  σ i β = isoToEquiv (iso fun inv σ-iso-sec σ-iso-ret)
    where
      σ-p0 σ-p1 : Fin N
      σ-p0 = weakenFin i
      σ-p1 = suc i

      σFinVec' : FinVec A N → (k : Fin N) → Dec (k ≡ σ-p0) → Dec (k ≡ σ-p1) → A
      σFinVec' f k (yes p0) d1         = equivFun (σ-flow (neg β)) (f σ-p1)
      σFinVec' f k (no np0) (yes p1)   = equivFun (σ-flow β) (f σ-p0)
      σFinVec' f k (no np0) (no np1)   = f k

      σFinVec : FinVec A N → FinVec A N
      σFinVec f k = σFinVec' f k (discreteFin k σ-p0) (discreteFin k σ-p1)

      -- funExt を使わず、区間変数 j と要素 k を直接束縛
      σFinVec-sq≡id : ∀ (f : FinVec A N) → σFinVec (σFinVec f) ≡ f
      σFinVec-sq≡id f j k = σFinVec-pointwise-sq k j
        where
        σFinVec≡f-when-outside : ∀ (g : FinVec A N) k → ¬ (k ≡ σ-p0) → ¬ (k ≡ σ-p1) → σFinVec g k ≡ g k
        σFinVec≡f-when-outside g k ¬p ¬q = help (discreteFin k σ-p0) (discreteFin k σ-p1)
          where
          help : (d0 : Dec (k ≡ σ-p0)) (d1 : Dec (k ≡ σ-p1)) → σFinVec' g k d0 d1 ≡ g k
          help (yes p) d1 = absurd-eqA (¬p p)
          help (no np0) (yes q) = absurd-eqA (¬q q)
          help (no np0) (no nq0) = refl

        σFinVec-at-p1 : ∀ g → σFinVec g σ-p1 ≡ equivFun (σ-flow β) (g σ-p0)
        σFinVec-at-p1 g = help (discreteFin σ-p1 σ-p0) (discreteFin σ-p1 σ-p1)
          where
          help : (d0 : Dec (σ-p1 ≡ σ-p0)) (d1 : Dec (σ-p1 ≡ σ-p1)) → σFinVec' g σ-p1 d0 d1 ≡ equivFun (σ-flow β) (g σ-p0)
          help (yes r) d1 = absurd-eqA (p0≢p1 i (sym r))
          help (no np0) (yes p1) = refl
          help (no np0) (no np) = absurd-eqA (np refl)

        σFinVec-at-p0 : ∀ g → σFinVec g σ-p0 ≡ equivFun (σ-flow (neg β)) (g σ-p1)
        σFinVec-at-p0 g = help (discreteFin σ-p0 σ-p0) (discreteFin σ-p0 σ-p1)
          where
          help : (d0 : Dec (σ-p0 ≡ σ-p0)) (d1 : Dec (σ-p0 ≡ σ-p1)) → σFinVec' g σ-p0 d0 d1 ≡ equivFun (σ-flow (neg β)) (g σ-p1)
          help (yes p0) d1 = refl
          help (no np) d1 = absurd-eqA (np refl)

        σFinVec-pointwise-sq : ∀ k → σFinVec (σFinVec f) k ≡ f k
        σFinVec-pointwise-sq k with discreteFin k σ-p0
        ... | yes p = cong (equivFun (σ-flow (neg β))) (σFinVec-at-p1 f) ∙ σ-neg-σ-pointwise β (f σ-p0) ∙ cong f (sym p)
        ... | no np0 with discreteFin k σ-p1
        ... | yes q = cong (equivFun (σ-flow β)) (σFinVec-at-p0 f) ∙ σ-σ-neg-pointwise β (f σ-p1) ∙ cong f (sym q)
        ... | no nq = σFinVec≡f-when-outside f k np0 nq

      fun : Vec A N → Vec A N
      fun v = FinVec→Vec (σFinVec (Vec→FinVec v))

      inv : Vec A N → Vec A N
      inv = fun

      -- ★ 余計なラッパーを脱ぎ捨てた、最も素直で美しいパスの結合
      σ-iso-sec σ-iso-ret : ∀ v → fun (inv v) ≡ v
      σ-iso-sec v = cong FinVec→Vec (cong σFinVec (FinVec→Vec→FinVec (σFinVec (Vec→FinVec v))))
                  ∙ cong FinVec→Vec (σFinVec-sq≡id (Vec→FinVec v))
                  ∙ Vec→FinVec→Vec v
      σ-iso-ret = σ-iso-sec

  -- ================================================================
  -- 3. ブレイド関係式（Phase 1 の仕上げ：後ほど FinVec で証明）
  -- ================================================================
  -- far-commute : ...
  -- braid-relation : ...