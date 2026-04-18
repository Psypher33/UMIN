{-# OPTIONS --cubical --guardedness --lossy-unification #-}
-- postulate（FarApart 等）を使うため --safe は付けない

module UMIN.L03_Dynamic.KMS.UMIN_ThermalBraid where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary.Base using (¬_; Dec; yes; no)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Data.Sigma using (_×_; ΣPathP)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (isoToEquiv; iso)
open import Cubical.Data.Vec using (Vec; _∷_; []; _++_; lookup; head; tail)
open import Cubical.Data.Vec.Properties using (FinVec→Vec; Vec→FinVec; Vec→FinVec→Vec; FinVec→Vec→FinVec)
open import Cubical.Data.Nat using (ℕ; zero; suc; _∸_)
open import Cubical.Data.Nat.Properties using (+-comm)
open import Cubical.Data.FinData.Base using (Fin; zero; suc; toℕ; weakenFin; ¬Fin0; FinVec)
open import Cubical.Data.FinData.Properties using (toℕ<n; weakenRespToℕ; discreteFin; injSucFin; znots)

-- 熱パラメータは ℤ；Nat の _+_ を開かない（β + γ が ℕ になるのを防ぐ）
open import Cubical.Data.Int using (ℤ; _+_)

open import UMIN.L02_Obstruction.Pi1.UMIN_TheoremB_Sublimated
open import UMIN.L04_Jones.YBE.UMIN_TheoremA_Sublimated

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

  -- FinVec 上の局所交差（核を1か所にまとめ、証明と定義が同じ式を指すようにする）
  σFinVec-core : (i : Fin (N ∸ 1)) (β : ℤ) (f : FinVec A N) (k : Fin N)
    → Dec (k ≡ weakenFin i) → Dec (k ≡ suc i) → A
  σFinVec-core i β f k (yes p0) d1       = equivFun (σ-flow (neg β)) (f (suc i))
  σFinVec-core i β f k (no np0) (yes p1) = equivFun (σ-flow β) (f (weakenFin i))
  σFinVec-core i β f k (no np0) (no np1) = f k

  σFinVec : (i : Fin (N ∸ 1)) (β : ℤ) → FinVec A N → FinVec A N
  σFinVec i β f k = σFinVec-core i β f k (discreteFin k (weakenFin i)) (discreteFin k (suc i))

  σFinVec-sq≡id : (i : Fin (N ∸ 1)) (β : ℤ) (f : FinVec A N) → σFinVec i β (σFinVec i β f) ≡ f
  σFinVec-sq≡id i β f j k = σFinVec-pointwise-sq k j
    where
    σ-p0 σ-p1 : Fin N
    σ-p0 = weakenFin i
    σ-p1 = suc i

    σFinVec≡f-when-outside : ∀ (g : FinVec A N) k → ¬ (k ≡ σ-p0) → ¬ (k ≡ σ-p1) → σFinVec i β g k ≡ g k
    σFinVec≡f-when-outside g k ¬p ¬q =
      help (discreteFin k σ-p0) (discreteFin k σ-p1)
      where
      help : (d0 : Dec (k ≡ σ-p0)) (d1 : Dec (k ≡ σ-p1)) → σFinVec-core i β g k d0 d1 ≡ g k
      help (yes p) d1 = absurd-eqA (¬p p)
      help (no np0) (yes q) = absurd-eqA (¬q q)
      help (no np0) (no nq0) = refl

    σFinVec-at-p1 : ∀ g → σFinVec i β g σ-p1 ≡ equivFun (σ-flow β) (g σ-p0)
    σFinVec-at-p1 g = help (discreteFin σ-p1 σ-p0) (discreteFin σ-p1 σ-p1)
      where
      help : (d0 : Dec (σ-p1 ≡ σ-p0)) (d1 : Dec (σ-p1 ≡ σ-p1)) → σFinVec-core i β g σ-p1 d0 d1 ≡ equivFun (σ-flow β) (g σ-p0)
      help (yes r) d1 = absurd-eqA (p0≢p1 i (sym r))
      help (no np0) (yes p1) = refl
      help (no np0) (no np) = absurd-eqA (np refl)

    σFinVec-at-p0 : ∀ g → σFinVec i β g σ-p0 ≡ equivFun (σ-flow (neg β)) (g σ-p1)
    σFinVec-at-p0 g = help (discreteFin σ-p0 σ-p0) (discreteFin σ-p0 σ-p1)
      where
      help : (d0 : Dec (σ-p0 ≡ σ-p0)) (d1 : Dec (σ-p0 ≡ σ-p1)) → σFinVec-core i β g σ-p0 d0 d1 ≡ equivFun (σ-flow (neg β)) (g σ-p1)
      help (yes p0) d1 = refl
      help (no np) d1 = absurd-eqA (np refl)

    σFinVec-pointwise-sq : ∀ k → σFinVec i β (σFinVec i β f) k ≡ f k
    σFinVec-pointwise-sq k with discreteFin k σ-p0
    ... | yes p = cong (equivFun (σ-flow (neg β))) (σFinVec-at-p1 f) ∙ σ-neg-σ-pointwise β (f σ-p0) ∙ cong f (sym p)
    ... | no np0 with discreteFin k σ-p1
    ... | yes q = cong (equivFun (σ-flow β)) (σFinVec-at-p0 f) ∙ σ-σ-neg-pointwise β (f σ-p1) ∙ cong f (sym q)
    ... | no nq = σFinVec≡f-when-outside f k np0 nq

  -- 2. 熱的ブレイド生成元 σ_i^β (FinVec 局所観測アプローチ)
  σ : (i : Fin (N ∸ 1)) (β : ℤ) → (Vec A N ≃ Vec A N)
  σ i β = isoToEquiv (iso fun inv σ-iso-sec σ-iso-ret)
    where
      fun : Vec A N → Vec A N
      fun v = FinVec→Vec (σFinVec i β (Vec→FinVec v))

      inv : Vec A N → Vec A N
      inv = fun

      σ-iso-sec σ-iso-ret : ∀ v → fun (inv v) ≡ v
      σ-iso-sec v =
          cong FinVec→Vec (cong (σFinVec i β) (FinVec→Vec→FinVec (σFinVec i β (Vec→FinVec v))))
        ∙ cong FinVec→Vec (σFinVec-sq≡id i β (Vec→FinVec v))
        ∙ Vec→FinVec→Vec v
      σ-iso-ret = σ-iso-sec

  -- ================================================================
  -- 3. ブレイド関係式（Phase 1 の仕上げ：後ほど FinVec で証明）
  -- ================================================================
  -- far-commute : ...
  -- braid-relation : ...
  -- ================================================================
  -- 4. 熱的ブレイド関係式 (The Quantum Braid Relations)
  -- ================================================================
  -- 幾何学的な「交差」と、KMS状態の「熱の移動(β, γ)」が完全に統合された
  -- 物理学・代数学における究極の保存則（Yang-Baxter方程式）です。

  -- ----------------------------------------------------------------
  -- ① 遠距離可換性 (Far-Commutativity)
  -- ----------------------------------------------------------------
  -- インデックスが 2 以上離れている場合（互いに干渉しない局所観測）、
  -- どの順序で熱的交差を行っても結果は完全に一致する。
  
  -- (※ 距離が2以上離れていることの補助的な型定義)
  -- toℕ i + 1 < toℕ j あるいは toℕ j + 1 < toℕ i であることを示す型を想定
  postulate
    FarApart : Fin (N ∸ 1) → Fin (N ∸ 1) → Type₀
    -- 交差領域が離れているときの局所可換性（FarApart の具体的意味と discreteFin による場合分けは未形式化）
    far-commute-pointwise :
      (i j : Fin (N ∸ 1)) (p : FarApart i j) (β γ : ℤ) (f : FinVec A N) (k : Fin N) →
      σFinVec i β (σFinVec j γ f) k ≡ σFinVec j γ (σFinVec i β f) k

  -- Equiv としての等式への引き上げ
  -- compEquiv f g の第1引数が先に作用し、第2引数が後（定義: g .fst ∘ f .fst）
  far-commute : (i j : Fin (N ∸ 1)) (p : FarApart i j) (β γ : ℤ) →
    compEquiv (σ j γ) (σ i β) ≡ compEquiv (σ i β) (σ j γ)
  far-commute i j p β γ =
    equivEq (funExt far-commute-path)
    where
    far-commute-path : (v : Vec A N) →
      equivFun (compEquiv (σ j γ) (σ i β)) v ≡ equivFun (compEquiv (σ i β) (σ j γ)) v
    far-commute-path v =
      let f₁ = σFinVec i β (Vec→FinVec v)
          g₁ = σFinVec j γ (Vec→FinVec v)
      in  congS FinVec→Vec (congS (σFinVec i β) (FinVec→Vec→FinVec g₁))
        ∙ congS FinVec→Vec (funExt (λ k → far-commute-pointwise i j p β γ (Vec→FinVec v) k))
        ∙ sym (congS FinVec→Vec (congS (σFinVec j γ) (FinVec→Vec→FinVec f₁)))
      
  -- ----------------------------------------------------------------
  -- ② 熱的ヤン・バクスター方程式 (Thermal Yang-Baxter Equation)
  -- ----------------------------------------------------------------
  -- 隣り合う交差 (i と i+1) における、3体散乱のエネルギー保存則。
  -- 前回の TheoremA であなたが討伐した `thermal-YBE` の成果を、
  -- この N 本の紐 (FinVec) の局所空間へと注入(受肉)させます！

  -- (※ i と i+1 を安全に扱うため、N ∸ 2 のインデックスを想定します)
  postulate
    -- i_next は i + 1 を指す補助関数（隣接ストランドのインデックス；具体定義は未固定）
    i_next : Fin (N ∸ 2) → Fin (N ∸ 1)
    i_curr : Fin (N ∸ 2) → Fin (N ∸ 1)
    -- TheoremA の thermal-YBE と 3 成分 (v1,v2,v3) を k 上で一致させるには
    -- i_curr / i_next と lookup の対応を明示する必要がある（現状は公理として置く）
    braid-relation-pointwise :
      (i : Fin (N ∸ 2)) (β γ : ℤ) (f : FinVec A N) (k : Fin N) →
      σFinVec (i_curr i) β (σFinVec (i_next i) (β + γ) (σFinVec (i_curr i) γ f)) k
      ≡
      σFinVec (i_next i) γ (σFinVec (i_curr i) (β + γ) (σFinVec (i_next i) β f)) k
    braid-relation :
      (i : Fin (N ∸ 2)) (β γ : ℤ) →
      compEquiv (σ (i_curr i) γ) (compEquiv (σ (i_next i) (β + γ)) (σ (i_curr i) β))
      ≡
      compEquiv (σ (i_next i) β) (compEquiv (σ (i_curr i) (β + γ)) (σ (i_next i) γ))
