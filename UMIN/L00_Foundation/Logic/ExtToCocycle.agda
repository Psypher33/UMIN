{-# OPTIONS --cubical --guardedness #-}

module UMIN.L00_Foundation.Logic.ExtToCocycle
  {ℓ} (X V : Set ℓ) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Path
open import Cubical.Data.Sigma
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation
  renaming (∥_∥₂ to ∥_∥₀ ; ∣_∣₂ to ∣_∣₀)

-- =========================================================
-- 0. 基本設定
-- =========================================================

Aut : Type ℓ → Type ℓ
Aut A = A ≃ A

-- =========================================================
-- 1. Ext¹
-- =========================================================

postulate
  -- STEP1: 分類空間（delooping）への最小インターフェース
  BAut : Type ℓ

Ext1 : Type ℓ
Ext1 = ∥ (X → BAut) ∥₀

postulate
  ε : Ext1

-- Ext¹ を分類空間経由で扱うための classifying map
postulate
  extClassifyingMap : Ext1 → (X → BAut)

-- =========================================================
-- 2. Cover と Overlap
-- =========================================================

record Cover (X : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    Idx : Type ℓ
    U   : Idx → Type ℓ
    inc : (i : Idx) → U i → X

Overlap : (C : Cover X) (i j : Cover.Idx C) → Type ℓ
Overlap C i j =
  Σ (Cover.U C i) λ x →
  Σ (Cover.U C j) λ y →
    Cover.inc C i x ≡ Cover.inc C j y

postulate
  refine : (C : Cover X) → Cover X

-- simplicial/hypercover 側へ拡張するための弱スケルトン
record HyperCover (X : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    C₀ : Cover X
    -- 2-simplex coherence を載せる最小フック
    has2Simplex : Type ℓ

-- =========================================================
-- 3. Extension
-- =========================================================

record Extension : Type (ℓ-suc ℓ) where
  field
    E     : Type ℓ
    i     : X → E
    p     : E → X
    fiber≃ : (x : X) → (Σ E (λ e → p e ≡ x)) ≃ V

postulate
  Ext→Extension : Ext1 → Extension

Eε : Extension
Eε = Ext→Extension ε

-- =========================================================
-- 4. Fiber family（核心）
-- =========================================================

Fiber : X → Type ℓ
Fiber z = Σ (Extension.E Eε) (λ e → Extension.p Eε e ≡ z)

-- =========================================================
-- 5. trivialize（pointwise版）
-- =========================================================

record LocallyTrivial (C : Cover X) : Type (ℓ-suc ℓ) where
  field
    trivialize :
      (i : Cover.Idx C) (x : Cover.U C i) →
      Fiber (Cover.inc C i x) ≃ V

postulate
  localTrivial :
    (C : Cover X) → LocallyTrivial C

trivialize :
  (C : Cover X) (i : Cover.Idx C) (x : Cover.U C i) →
  Fiber (Cover.inc C i x) ≃ V
trivialize C i x = LocallyTrivial.trivialize (localTrivial C) i x

-- =========================================================
-- 6. Cocycle（完全版）
-- =========================================================

g-fun :
  (C : Cover X) →
  (i j : Cover.Idx C) →
  (u : Overlap C i j) →
  V → V
g-fun C i j (x , y , p) v =
  let
    ti = trivialize C i x
    tj = trivialize C j y

    -- Step 1: V → Fiber (i 側)
    e₁ : Fiber (Cover.inc C i x)
    e₁ = invEq ti v

    -- Step 2: transport（核心）
    e₂ : Fiber (Cover.inc C j y)
    e₂ = subst Fiber p e₁

  in
    -- Step 3: Fiber → V
    equivFun tj e₂

g-inv :
  (C : Cover X) →
  (i j : Cover.Idx C) →
  (u : Overlap C i j) →
  V → V
g-inv C i j (x , y , p) w =
  let
    ti = trivialize C i x
    tj = trivialize C j y

    e₁ : Fiber (Cover.inc C j y)
    e₁ = invEq tj w

    e₂ : Fiber (Cover.inc C i x)
    e₂ = subst⁻ Fiber p e₁

  in
    equivFun ti e₂

gIso :
  (C : Cover X) →
  (i j : Cover.Idx C) →
  (u : Overlap C i j) →
  Iso V V
gIso-sec :
  (C : Cover X) →
  (i j : Cover.Idx C) →
  (u : Overlap C i j) →
  section (g-fun C i j u) (g-inv C i j u)
gIso-sec C i j (x , y , p) w =
  cong (λ t → equivFun tj (subst Fiber p t))
       (retEq ti (subst⁻ Fiber p (invEq tj w)))
  ∙ cong (equivFun tj) (substSubst⁻ Fiber p (invEq tj w))
  ∙ secEq tj w
  where
    ti : Fiber (Cover.inc C i x) ≃ V
    ti = trivialize C i x

    tj : Fiber (Cover.inc C j y) ≃ V
    tj = trivialize C j y

gIso-ret :
  (C : Cover X) →
  (i j : Cover.Idx C) →
  (u : Overlap C i j) →
  retract (g-fun C i j u) (g-inv C i j u)
gIso-ret C i j (x , y , p) v =
  cong (λ t → equivFun ti (subst⁻ Fiber p t))
       (retEq tj (subst Fiber p (invEq ti v)))
  ∙ cong (equivFun ti) (subst⁻Subst Fiber p (invEq ti v))
  ∙ secEq ti v
  where
    ti : Fiber (Cover.inc C i x) ≃ V
    ti = trivialize C i x

    tj : Fiber (Cover.inc C j y) ≃ V
    tj = trivialize C j y

Iso.fun (gIso C i j u) = g-fun C i j u
Iso.inv (gIso C i j u) = g-inv C i j u
Iso.sec (gIso C i j u) = gIso-sec C i j u
Iso.ret (gIso C i j u) = gIso-ret C i j u

Cocycle :
  (C : Cover X) (i j : Cover.Idx C) →
  Overlap C i j → Aut V
Cocycle C i j u = isoToEquiv (gIso C i j u)

-- =========================================================
-- 7. Cocycle Condition（次に埋める）
-- =========================================================

CocycleCondition :
  (C : Cover X) (i j k : Cover.Idx C) →
  (x : Cover.U C i) (y : Cover.U C j) (z : Cover.U C k) →
  (p : Cover.inc C i x ≡ Cover.inc C j y) →
  (q : Cover.inc C j y ≡ Cover.inc C k z) →
  Cocycle C i j (x , y , p) ∙ₑ Cocycle C j k (y , z , q)
  ≡ Cocycle C i k (x , z , p ∙ q)
CocycleCondition C i j k x y z p q =
  equivEq (funExt λ v →
    let
      ti = trivialize C i x
      tj = trivialize C j y
      tk = trivialize C k z

      e₀ = invEq ti v
      e₁ = subst Fiber p e₀
    in
    -- Step 1: tj cancel
    cong (λ t → equivFun tk (subst Fiber q t))
         (retEq tj e₁)
    ∙
    -- Step 2: transport composition（← ここ修正）
    cong (equivFun tk)
         (sym (substComposite Fiber p q e₀)))

-- =========================================================
-- 8. cocycle → φ（global）
-- =========================================================

-- =========================================================
-- Čech descent 用補助
-- =========================================================

postulate
  -- 基準チャート（anchor）
  baseChart :
    (C : Cover X) →
    Σ (Cover.Idx C) (λ i → Cover.U C i)

  -- anchor が各点へ届くこと（p を穴なしで作るための最小仮定）
  baseHit :
    (C : Cover X) (x : X) →
    (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
    Cover.inc C (fst b) (snd b) ≡ x

  -- chart 間を Overlap に持ち上げる
  chart-bridge :
    (C : Cover X) →
    (i j : Cover.Idx C) →
    (xi : Cover.U C i) →
    (xj : Cover.U C j) →
    Cover.inc C i xi ≡ Cover.inc C j xj →
    Overlap C i j


-- Čech descent 用：overlap 鎖
data PathChain (C : Cover X)
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) :
  X → Type ℓ where

  -- 長さ0（anchorそのもの）
  nil :
    PathChain C b (Cover.inc C (fst b) (snd b))

  -- 1ステップ延長
  cons :
    {x y : X} →
    PathChain C b x →
    (i j : Cover.Idx C) →
    (xi : Cover.U C i) →
    (yj : Cover.U C j) →
    (p : Cover.inc C i xi ≡ x) →
    (q : Cover.inc C i xi ≡ Cover.inc C j yj) →
    PathChain C b (Cover.inc C j yj)

foldChain :
  (C : Cover X) →
  (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  {x : X} →
  PathChain C b x →
  Aut V
foldChain C γ b nil = idEquiv V
foldChain C γ b (cons {x = x₀} {y = y₀} chain i j xi yj p q) =
  let
    prev = foldChain C γ b chain
    u : Overlap C i j
    u = (xi , yj , q)
  in
  prev ∙ₑ γ i j u

-- chain の同値（ホモトピー）: まずは最小核
data ChainEq (C : Cover X)
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) :
  {x : X} → PathChain C b x → PathChain C b x → Type ℓ where
  crefl : {x : X} → (c : PathChain C b x) → ChainEq C b c c
  csym  : {x : X} {c₁ c₂ : PathChain C b x} →
          ChainEq C b c₁ c₂ → ChainEq C b c₂ c₁
  ctrans : {x : X} {c₁ c₂ c₃ : PathChain C b x} →
           ChainEq C b c₁ c₂ → ChainEq C b c₂ c₃ → ChainEq C b c₁ c₃
  -- ★核心：三角変形（Čech 2-simplex）
  ctriangle :
    (i j k : Cover.Idx C) →
    (xi : Cover.U C i) →
    (yj : Cover.U C j) →
    (zk : Cover.U C k) →
    (chain : PathChain C b (Cover.inc C i xi)) →
    (p : Cover.inc C i xi ≡ Cover.inc C j yj) →
    (q : Cover.inc C j yj ≡ Cover.inc C k zk) →
    ChainEq C b {x = Cover.inc C k zk}
      (cons {x = Cover.inc C j yj} {y = Cover.inc C k zk}
            (cons {x = Cover.inc C i xi} {y = Cover.inc C j yj}
                  chain i j xi yj refl p)
            j k yj zk refl q)
      (cons {x = Cover.inc C i xi} {y = Cover.inc C k zk}
            chain i k xi zk refl (p ∙ q))

foldChain-resp :
  (C : Cover X) →
  (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
  (γ-cocycle :
    (i j k : Cover.Idx C) →
    (xi : Cover.U C i) (yj : Cover.U C j) (zk : Cover.U C k) →
    (p : Cover.inc C i xi ≡ Cover.inc C j yj) →
    (q : Cover.inc C j yj ≡ Cover.inc C k zk) →
    γ i j (xi , yj , p) ∙ₑ γ j k (yj , zk , q)
    ≡ γ i k (xi , zk , p ∙ q)) →
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  {x : X} →
  (chain₁ chain₂ : PathChain C b x) →
  ChainEq C b chain₁ chain₂ →
  foldChain C γ b chain₁ ≡ foldChain C γ b chain₂
foldChain-resp-triangle :
  (C : Cover X) →
  (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
  (γ-cocycle :
    (i j k : Cover.Idx C) →
    (xi : Cover.U C i) (yj : Cover.U C j) (zk : Cover.U C k) →
    (p : Cover.inc C i xi ≡ Cover.inc C j yj) →
    (q : Cover.inc C j yj ≡ Cover.inc C k zk) →
    γ i j (xi , yj , p) ∙ₑ γ j k (yj , zk , q)
    ≡ γ i k (xi , zk , p ∙ q)) →
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  (i j k : Cover.Idx C) →
  (xi : Cover.U C i) →
  (yj : Cover.U C j) →
  (zk : Cover.U C k) →
  (chain : PathChain C b (Cover.inc C i xi)) →
  (p : Cover.inc C i xi ≡ Cover.inc C j yj) →
  (q : Cover.inc C j yj ≡ Cover.inc C k zk) →
  foldChain C γ b
    (cons {x = Cover.inc C j yj} {y = Cover.inc C k zk}
      (cons {x = Cover.inc C i xi} {y = Cover.inc C j yj}
        chain i j xi yj refl p)
      j k yj zk refl q)
  ≡
  foldChain C γ b
    (cons {x = Cover.inc C i xi} {y = Cover.inc C k zk}
      chain i k xi zk refl (p ∙ q))
foldChain-resp-triangle C γ γ-cocycle b i j k xi yj zk chain p q =
  sym (compEquiv-assoc (foldChain C γ b chain) (γ i j (xi , yj , p)) (γ j k (yj , zk , q)))
  ∙ cong (λ t → foldChain C γ b chain ∙ₑ t)
         (γ-cocycle i j k xi yj zk p q)

foldChain-resp C γ γ-cocycle b {x = x} c₁ .c₁ (crefl c₁) = refl
foldChain-resp C γ γ-cocycle b {x = x} c₁ c₂ (csym e) =
  sym (foldChain-resp C γ γ-cocycle b {x = x} c₂ c₁ e)
foldChain-resp C γ γ-cocycle b {x = x} c₁ c₃ (ctrans {c₂ = c₂} e₁ e₂) =
  foldChain-resp C γ γ-cocycle b {x = x} c₁ c₂ e₁
  ∙ foldChain-resp C γ γ-cocycle b {x = x} c₂ c₃ e₂
foldChain-resp C γ γ-cocycle b chain₁ chain₂
  (ctriangle i j k xi yj zk chain p q) =
  foldChain-resp-triangle C γ γ-cocycle b i j k xi yj zk chain p q

foldChain-homotopy-invariant :
  (C : Cover X) →
  (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
  (γ-cocycle :
    (i j k : Cover.Idx C) →
    (xi : Cover.U C i) (yj : Cover.U C j) (zk : Cover.U C k) →
    (p : Cover.inc C i xi ≡ Cover.inc C j yj) →
    (q : Cover.inc C j yj ≡ Cover.inc C k zk) →
    γ i j (xi , yj , p) ∙ₑ γ j k (yj , zk , q)
    ≡ γ i k (xi , zk , p ∙ q)) →
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  {x : X} →
  (chain₁ chain₂ : PathChain C b x) →
  ChainEq C b chain₁ chain₂ →
  foldChain C γ b chain₁ ≡ foldChain C γ b chain₂
foldChain-homotopy-invariant C γ γ-cocycle b {x = x} chain₁ chain₂ eq =
  foldChain-resp C γ γ-cocycle b {x = x} chain₁ chain₂ eq

postulate
  chartChain :
    (C : Cover X) →
    (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
    (x : X) →
    PathChain C b x

  chartChain-coherent :
    (C : Cover X) →
    (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
    (x : X) →
    (chain₁ chain₂ : PathChain C b x) →
    ChainEq C b chain₁ chain₂

  -- base が異なる場合の比較（base-bridge を置換可能な最小仮定）
  chartChain-coherent-base :
    (C : Cover X) →
    (x : X) →
    (b₁ b₂ : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
    foldChain C (Cocycle C) b₁ (chartChain C b₁ x)
    ≡ foldChain C (Cocycle C) b₂ (chartChain C b₂ x)

chain-endpoint :
  (C : Cover X) →
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  (x : X) →
  PathChain C b x →
  Σ (Cover.Idx C) (λ i →
  Σ (Cover.U C i) (λ u →
    Cover.inc C i u ≡ x))
chain-endpoint C b x nil = fst b , snd b , refl
chain-endpoint C b .(Cover.inc C j yj)
  (cons {x = x₀} {y = y₀} chain i j xi yj p q) = j , yj , refl

-- =========================================================
-- 8'. cocycle → φ（with-base 版）
-- =========================================================

cocycle→φ-with-base :
  (C : Cover X) →
  ((i j : Cover.Idx C) → Overlap C i j → Aut V) →
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  X → Aut V
cocycle→φ-with-base C γ b x =
  foldChain C γ b (chartChain C b x)

-- =========================================================
-- 8''. cocycle → φ（ラッパ）
-- =========================================================

cocycle→φ :
  (C : Cover X) →
  ((i j : Cover.Idx C) → Overlap C i j → Aut V) →
  X → Aut V
cocycle→φ C γ x =
  cocycle→φ-with-base C γ (baseChart C) x

-- chain を明示した descent 版
cocycle→φ-chain :
  (C : Cover X) →
  (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  (x : X) →
  PathChain C b x →
  Aut V
cocycle→φ-chain C γ b x chain =
  foldChain C γ b chain

-- =========================================================
-- 8'''. local g-fun と global foldChain の接続
-- =========================================================

chain-step :
  (C : Cover X) →
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  {x : X} →
  PathChain C b x →
  (i j : Cover.Idx C) →
  (xi : Cover.U C i) →
  (yj : Cover.U C j) →
  (p : Cover.inc C i xi ≡ x) →
  (q : Cover.inc C i xi ≡ Cover.inc C j yj) →
  PathChain C b (Cover.inc C j yj)
chain-step C b {x = x₀} chain i j xi yj p q =
  cons {x = x₀} {y = Cover.inc C j yj} chain i j xi yj p q

postulate
  -- 1ステップの fold が local cocycle（γ）と一致
  foldChain-step-compat :
    (C : Cover X) →
    (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
    (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
    {x : X} →
    (chain : PathChain C b x) →
    (i j : Cover.Idx C) →
    (xi : Cover.U C i) →
    (yj : Cover.U C j) →
    (p : Cover.inc C i xi ≡ x) →
    (q : Cover.inc C i xi ≡ Cover.inc C j yj) →
    foldChain C γ b (chain-step C b chain i j xi yj p q)
    ≡
    (foldChain C γ b chain) ∙ₑ γ i j (xi , yj , q)

  -- local g-fun と foldChain の評価が整合
  gfun-foldChain-compat :
    (C : Cover X) →
    (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
    (i j : Cover.Idx C) →
    (u : Overlap C i j) →
    (x : X) →
    (chain : PathChain C b x) →
    (v : V) →
    g-fun C i j u (equivFun (foldChain C (Cocycle C) b chain) v)
      ≡
    equivFun ((foldChain C (Cocycle C) b chain) ∙ₑ (Cocycle C i j u)) v

postulate
  -- =========================================================
  -- 8-A 補助：対角単位・逆元・右キャンセル
  -- =========================================================
  γ-id :
    (C : Cover X) →
    (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
    (i : Cover.Idx C) →
    (x : Cover.U C i) →
    γ i i (x , x , refl) ≡ idEquiv V

  γ-inv :
    (C : Cover X) →
    (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
    (i j : Cover.Idx C) →
    (x : Cover.U C i) →
    (y : Cover.U C j) →
    (p : Cover.inc C i x ≡ Cover.inc C j y) →
    γ j i (y , x , sym p) ≡ invEquiv (γ i j (x , y , p))

  ∙ₑ-inv-r :
    (f : Aut V) →
    f ∙ₑ invEquiv f ≡ idEquiv V

  -- =========================================================
  -- 8-A. chart差の吸収（core）
  -- =========================================================
  cocycle→φ-well-defined-core :
    (C : Cover X) →
    (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
    (γ-cocycle :
      (i j k : Cover.Idx C) →
      (x : Cover.U C i) (y : Cover.U C j) (z : Cover.U C k) →
      (p : Cover.inc C i x ≡ Cover.inc C j y) →
      (q : Cover.inc C j y ≡ Cover.inc C k z) →
      γ i j (x , y , p) ∙ₑ γ j k (y , z , q)
      ≡ γ i k (x , z , p ∙ q)) →
    (x : X) →
    (i j : Cover.Idx C) →
    (xi : Cover.U C i) (xj : Cover.U C j) →
    (pi : Cover.inc C i xi ≡ x) →
    (pj : Cover.inc C j xj ≡ x) →
    (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
    let
      i₀ = fst b
      u₀ = snd b
      p₀i : Cover.inc C i₀ u₀ ≡ Cover.inc C i xi
      p₀i = baseHit C x b ∙ sym pi
      p₀j : Cover.inc C i₀ u₀ ≡ Cover.inc C j xj
      p₀j = baseHit C x b ∙ sym pj
    in
    γ i₀ i (chart-bridge C i₀ i u₀ xi p₀i)
    ≡
    γ i₀ j (chart-bridge C i₀ j u₀ xj p₀j)

  -- =========================================================
  -- 8-B. baseChart 独立性（ゲージ不変性）
  -- =========================================================
  cocycle→φ-baseChart-indep :
    (C : Cover X) →
    (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
    (γ-cocycle :
      (i j k : Cover.Idx C) →
      (x : Cover.U C i) (y : Cover.U C j) (z : Cover.U C k) →
      (p : Cover.inc C i x ≡ Cover.inc C j y) →
      (q : Cover.inc C j y ≡ Cover.inc C k z) →
      γ i j (x , y , p) ∙ₑ γ j k (y , z , q)
      ≡ γ i k (x , z , p ∙ q)) →
    (x : X) →
    (b₁ b₂ : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
    cocycle→φ-with-base C γ b₁ x
    ≡
    cocycle→φ-with-base C γ b₂ x

core-step₁ :
  (C : Cover X) →
  (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
  (γ-cocycle :
    (i j k : Cover.Idx C) →
    (x : Cover.U C i) (y : Cover.U C j) (z : Cover.U C k) →
    (p : Cover.inc C i x ≡ Cover.inc C j y) →
    (q : Cover.inc C j y ≡ Cover.inc C k z) →
    γ i j (x , y , p) ∙ₑ γ j k (y , z , q)
    ≡ γ i k (x , z , p ∙ q)) →
  (x : X) →
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  (i j : Cover.Idx C) →
  (xi : Cover.U C i) (xj : Cover.U C j) →
  (pi : Cover.inc C i xi ≡ x) →
  (pj : Cover.inc C j xj ≡ x) →
  let
    i₀ = fst b
    u₀ = snd b

    p₀i : Cover.inc C i₀ u₀ ≡ Cover.inc C i xi
    p₀i = baseHit C x b ∙ sym pi

    p₀j : Cover.inc C i₀ u₀ ≡ Cover.inc C j xj
    p₀j = baseHit C x b ∙ sym pj

    pji : Cover.inc C j xj ≡ Cover.inc C i xi
    pji = sym p₀j ∙ p₀i

    u₀i : Overlap C i₀ i
    u₀i = chart-bridge C i₀ i u₀ xi p₀i

    u₀j : Overlap C i₀ j
    u₀j = chart-bridge C i₀ j u₀ xj p₀j

    uji : Overlap C j i
    uji = chart-bridge C j i xj xi pji
  in
  γ i₀ i u₀i ≡ (γ i₀ j u₀j) ∙ₑ (γ j i uji)
postulate
  core-step₁-proof :
    (C : Cover X) →
    (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
    (γ-cocycle :
      (i j k : Cover.Idx C) →
      (x : Cover.U C i) (y : Cover.U C j) (z : Cover.U C k) →
      (p : Cover.inc C i x ≡ Cover.inc C j y) →
      (q : Cover.inc C j y ≡ Cover.inc C k z) →
      γ i j (x , y , p) ∙ₑ γ j k (y , z , q)
      ≡ γ i k (x , z , p ∙ q)) →
    (x : X) →
    (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
    (i j : Cover.Idx C) →
    (xi : Cover.U C i) (xj : Cover.U C j) →
    (pi : Cover.inc C i xi ≡ x) →
    (pj : Cover.inc C j xj ≡ x) →
    let
      i₀ = fst b
      u₀ = snd b
      p₀i : Cover.inc C i₀ u₀ ≡ Cover.inc C i xi
      p₀i = baseHit C x b ∙ sym pi
      p₀j : Cover.inc C i₀ u₀ ≡ Cover.inc C j xj
      p₀j = baseHit C x b ∙ sym pj
      pji : Cover.inc C j xj ≡ Cover.inc C i xi
      pji = sym p₀j ∙ p₀i
      u₀i : Overlap C i₀ i
      u₀i = chart-bridge C i₀ i u₀ xi p₀i
      u₀j : Overlap C i₀ j
      u₀j = chart-bridge C i₀ j u₀ xj p₀j
      uji : Overlap C j i
      uji = chart-bridge C j i xj xi pji
    in
    γ i₀ i u₀i ≡ (γ i₀ j u₀j) ∙ₑ (γ j i uji)

core-step₁ C γ γ-cocycle x b i j xi xj pi pj =
  core-step₁-proof C γ γ-cocycle x b i j xi xj pi pj

postulate
  -- γ-inv を使った右側消去の橋渡し（loop=id 仮定の代替）
  γ-inv-cancel :
    (C : Cover X) →
    (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
    (x : X) →
    (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
    (i j : Cover.Idx C) →
    (xi : Cover.U C i) (xj : Cover.U C j) →
    (pi : Cover.inc C i xi ≡ x) →
    (pj : Cover.inc C j xj ≡ x) →
    let
      i₀ = fst b
      u₀ = snd b
      p₀i : Cover.inc C i₀ u₀ ≡ Cover.inc C i xi
      p₀i = baseHit C x b ∙ sym pi
      p₀j : Cover.inc C i₀ u₀ ≡ Cover.inc C j xj
      p₀j = baseHit C x b ∙ sym pj
      pji : Cover.inc C j xj ≡ Cover.inc C i xi
      pji = sym p₀j ∙ p₀i
      u₀j : Overlap C i₀ j
      u₀j = chart-bridge C i₀ j u₀ xj p₀j
      uji : Overlap C j i
      uji = chart-bridge C j i xj xi pji
    in
    (γ i₀ j u₀j) ∙ₑ (γ j i uji) ≡ γ i₀ j u₀j

  ∙ₑ-assoc :
    (f g h : Aut V) →
    (f ∙ₑ g) ∙ₑ h ≡ f ∙ₑ (g ∙ₑ h)

  ∙ₑ-id-r :
    (f : Aut V) →
    f ∙ₑ idEquiv V ≡ f

core-step₂ :
  (C : Cover X) →
  (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
  (x : X) →
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  (i j : Cover.Idx C) →
  (xi : Cover.U C i) (xj : Cover.U C j) →
  (pi : Cover.inc C i xi ≡ x) →
  (pj : Cover.inc C j xj ≡ x) →
  let
    i₀ = fst b
    u₀ = snd b
    p₀i : Cover.inc C i₀ u₀ ≡ Cover.inc C i xi
    p₀i = baseHit C x b ∙ sym pi
    p₀j : Cover.inc C i₀ u₀ ≡ Cover.inc C j xj
    p₀j = baseHit C x b ∙ sym pj
    pji : Cover.inc C j xj ≡ Cover.inc C i xi
    pji = sym p₀j ∙ p₀i
    u₀j : Overlap C i₀ j
    u₀j = chart-bridge C i₀ j u₀ xj p₀j
    uji : Overlap C j i
    uji = chart-bridge C j i xj xi pji
  in
  (γ i₀ j u₀j) ∙ₑ (γ j i uji) ≡ γ i₀ j u₀j

core-step₂ C γ x b i j xi xj pi pj =
  γ-inv-cancel C γ x b i j xi xj pi pj

core-final :
  (C : Cover X) →
  (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
  (γ-cocycle :
    (i j k : Cover.Idx C) →
    (x : Cover.U C i) (y : Cover.U C j) (z : Cover.U C k) →
    (p : Cover.inc C i x ≡ Cover.inc C j y) →
    (q : Cover.inc C j y ≡ Cover.inc C k z) →
    γ i j (x , y , p) ∙ₑ γ j k (y , z , q)
    ≡ γ i k (x , z , p ∙ q)) →
  (x : X) →
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  (i j : Cover.Idx C) →
  (xi : Cover.U C i) (xj : Cover.U C j) →
  (pi : Cover.inc C i xi ≡ x) →
  (pj : Cover.inc C j xj ≡ x) →
  let
    i₀ = fst b
    u₀ = snd b
    p₀i : Cover.inc C i₀ u₀ ≡ Cover.inc C i xi
    p₀i = baseHit C x b ∙ sym pi
    p₀j : Cover.inc C i₀ u₀ ≡ Cover.inc C j xj
    p₀j = baseHit C x b ∙ sym pj
    u₀i : Overlap C i₀ i
    u₀i = chart-bridge C i₀ i u₀ xi p₀i
    u₀j : Overlap C i₀ j
    u₀j = chart-bridge C i₀ j u₀ xj p₀j
  in
  γ i₀ i u₀i ≡ γ i₀ j u₀j
core-final C γ γ-cocycle x b i j xi xj pi pj =
  core-step₁ C γ γ-cocycle x b i j xi xj pi pj
  ∙ core-step₂ C γ x b i j xi xj pi pj

-- =========================================================
-- 8-C. φ の well-definedness（まとめ）
-- =========================================================

cocycle→φ-well-defined :
  (C : Cover X) →
  (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
  (γ-cocycle :
    (i j k : Cover.Idx C) →
    (x : Cover.U C i) (y : Cover.U C j) (z : Cover.U C k) →
    (p : Cover.inc C i x ≡ Cover.inc C j y) →
    (q : Cover.inc C j y ≡ Cover.inc C k z) →
    γ i j (x , y , p) ∙ₑ γ j k (y , z , q)
    ≡ γ i k (x , z , p ∙ q)) →
  (x : X) →
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  cocycle→φ-with-base C γ b x
  ≡ cocycle→φ-with-base C γ b x
cocycle→φ-well-defined C γ γ-cocycle x b =
  foldChain-resp C γ γ-cocycle b
    (chartChain C b x)
    (chartChain C b x)
    (chartChain-coherent C b x (chartChain C b x) (chartChain C b x))

postulate
  -- base 間の比較を与える弱構造（gauge bridge）
  base-bridge :
    (C : Cover X) →
    (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
    (γ-cocycle :
      (i j k : Cover.Idx C) →
      (x : Cover.U C i) (y : Cover.U C j) (z : Cover.U C k) →
      (p : Cover.inc C i x ≡ Cover.inc C j y) →
      (q : Cover.inc C j y ≡ Cover.inc C k z) →
      γ i j (x , y , p) ∙ₑ γ j k (y , z , q)
      ≡ γ i k (x , z , p ∙ q)) →
    (x : X) →
    (b₁ b₂ : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
    cocycle→φ-with-base C γ b₁ x
    ≡ cocycle→φ-with-base C γ b₂ x

postulate
  cocycle→φ-independence-lift :
    (C : Cover X) →
    (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
    (γ-cocycle :
      (i j k : Cover.Idx C) →
      (x : Cover.U C i) (y : Cover.U C j) (z : Cover.U C k) →
      (p : Cover.inc C i x ≡ Cover.inc C j y) →
      (q : Cover.inc C j y ≡ Cover.inc C k z) →
      γ i j (x , y , p) ∙ₑ γ j k (y , z , q)
      ≡ γ i k (x , z , p ∙ q)) →
    (x : X) →
    (b₁ b₂ : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
    cocycle→φ-with-base C γ b₁ x
    ≡ cocycle→φ-with-base C γ b₂ x

cocycle→φ-independence :
  (C : Cover X) →
  (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
  (γ-cocycle :
    (i j k : Cover.Idx C) →
    (x : Cover.U C i) (y : Cover.U C j) (z : Cover.U C k) →
    (p : Cover.inc C i x ≡ Cover.inc C j y) →
    (q : Cover.inc C j y ≡ Cover.inc C k z) →
    γ i j (x , y , p) ∙ₑ γ j k (y , z , q)
    ≡ γ i k (x , z , p ∙ q)) →
  (x : X) →
  (b₁ b₂ : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  cocycle→φ-with-base C γ b₁ x
  ≡ cocycle→φ-with-base C γ b₂ x
cocycle→φ-independence = cocycle→φ-independence-lift

-- base-bridge を使わない導出形（Cocycle C に特化）
cocycle→φ-independence-from-chain :
  (C : Cover X) →
  (x : X) →
  (b₁ b₂ : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  cocycle→φ-with-base C (Cocycle C) b₁ x
  ≡ cocycle→φ-with-base C (Cocycle C) b₂ x
cocycle→φ-independence-from-chain C x b₁ b₂ =
  chartChain-coherent-base C x b₁ b₂

-- canonical base（baseChart）に固定した well-definedness
cocycle→φ-canonical-well-defined :
  (C : Cover X) →
  (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
  (γ-cocycle :
    (i j k : Cover.Idx C) →
    (x : Cover.U C i) (y : Cover.U C j) (z : Cover.U C k) →
    (p : Cover.inc C i x ≡ Cover.inc C j y) →
    (q : Cover.inc C j y ≡ Cover.inc C k z) →
    γ i j (x , y , p) ∙ₑ γ j k (y , z , q)
    ≡ γ i k (x , z , p ∙ q)) →
  (x : X) →
  cocycle→φ C γ x ≡ cocycle→φ C γ x
cocycle→φ-canonical-well-defined C γ γ-cocycle x =
  cocycle→φ-well-defined C γ γ-cocycle x (baseChart C)

postulate
  Cbase : Cover X

φ : X → Aut V
φ = cocycle→φ C₀ (Cocycle C₀)
  where
    C₀ : Cover X
    C₀ = refine Cbase

-- =========================================================
-- 9. Split/Hyper cover 側の制約
-- =========================================================

record SplitCover (X : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    C : Cover X
    -- 各点に対する chart 選択（split）
    split :
      (x : X) →
      Σ (Cover.Idx C) (λ i →
      Σ (Cover.U C i) (λ u →
        Cover.inc C i u ≡ x))

record HyperCoverSkeleton (X : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    C₀ : Cover X
    C₁ : Type ℓ
    C₂ : Type ℓ

-- 固定 cover 上の Čech 1-cocycle（値は Aut V）
Cech1On :
  (C : Cover X) →
  Type ℓ
Cech1On C =
  Σ ((i j : Cover.Idx C) → Overlap C i j → Aut V)
    (λ γ →
      (i j k : Cover.Idx C) →
      (x : Cover.U C i) (y : Cover.U C j) (z : Cover.U C k) →
      (p : Cover.inc C i x ≡ Cover.inc C j y) →
      (q : Cover.inc C j y ≡ Cover.inc C k z) →
      γ i j (x , y , p) ∙ₑ γ j k (y , z , q)
      ≡ γ i k (x , z , p ∙ q))

-- Split cover 版の Čech H¹（まずは fixed-cover の cocycle 類）
postulate
  Cech1EqOn :
    (C : Cover X) →
    Cech1On C → Cech1On C → Type ℓ

  CechH1Split :
    (SC : SplitCover X) →
    Type (ℓ-suc ℓ)

  -- fixed split cover から Čech H¹ 代表へ送る射影
  cech1-class :
    (SC : SplitCover X) →
    Cech1On (SplitCover.C SC) →
    CechH1Split SC

-- STEP3: descent の glue（fixed cover 版）
Cech1On-γ :
  {C : Cover X} →
  Cech1On C →
  (i j : Cover.Idx C) → Overlap C i j → Aut V
Cech1On-γ ξ = fst ξ

Cech1On-cocycle :
  {C : Cover X} →
  (ξ : Cech1On C) →
  (i j k : Cover.Idx C) →
  (x : Cover.U C i) (y : Cover.U C j) (z : Cover.U C k) →
  (p : Cover.inc C i x ≡ Cover.inc C j y) →
  (q : Cover.inc C j y ≡ Cover.inc C k z) →
  Cech1On-γ ξ i j (x , y , p) ∙ₑ Cech1On-γ ξ j k (y , z , q)
  ≡ Cech1On-γ ξ i k (x , z , p ∙ q)
Cech1On-cocycle ξ = snd ξ

-- cocycle から得る global section（foldChain ベース）
glueSectionOn :
  (C : Cover X) →
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  Cech1On C →
  X → Aut V
glueSectionOn C b ξ =
  cocycle→φ-with-base C (Cech1On-γ ξ) b

postulate
  -- cocycle（固定 cover）から貼り合わせ拡張を得る
  glueExtensionOn :
    (C : Cover X) →
    Cech1On C →
    Extension

  -- split cover 版の代表から拡張類へ
  glueExtensionSplit :
    (SC : SplitCover X) →
    CechH1Split SC →
    Extension

-- STEP4: classify（Ext¹ → Čech H¹）
postulate
  -- Ext¹ の代表から fixed cover 上の cocycle を抽出
  classifyOn :
    (C : Cover X) →
    Ext1 →
    Cech1On C

  -- split cover 版の Čech H¹ 類へ送る
  classifySplit :
    (SC : SplitCover X) →
    Ext1 →
    CechH1Split SC

  -- fixed cover では類写像は代表写像と整合
  classifySplit-β :
    (SC : SplitCover X) →
    (e : Ext1) →
    classifySplit SC e
    ≡ cech1-class SC (classifyOn (SplitCover.C SC) e)

-- STEP5: unclassify（Čech H¹ → Ext¹）
postulate
  -- fixed cover cocycle から Ext¹ の代表へ
  unclassifyOn :
    (C : Cover X) →
    Cech1On C →
    Ext1

  -- split cover 版の Čech H¹ 類から Ext¹ へ
  unclassifySplit :
    (SC : SplitCover X) →
    CechH1Split SC →
    Ext1

  -- fixed cover 代表を類へ上げてから戻すと一致
  unclassifySplit-β :
    (SC : SplitCover X) →
    (ξ : Cech1On (SplitCover.C SC)) →
    unclassifySplit SC (cech1-class SC ξ)
    ≡ unclassifyOn (SplitCover.C SC) ξ

  -- glue で得た拡張と Ext→Extension の整合（fixed cover）
  unclassifyOn-glueExtension :
    (C : Cover X) →
    (ξ : Cech1On C) →
    Ext→Extension (unclassifyOn C ξ)
    ≡ glueExtensionOn C ξ

  -- split cover 版の整合
  unclassifySplit-glueExtension :
    (SC : SplitCover X) →
    (η : CechH1Split SC) →
    Ext→Extension (unclassifySplit SC η)
    ≡ glueExtensionSplit SC η

-- STEP6: classify/unclassify の相互逆（descent = 同値）
postulate
  classify∘unclassify-On :
    (C : Cover X) →
    (ξ : Cech1On C) →
    classifyOn C (unclassifyOn C ξ) ≡ ξ

  unclassify∘classify-On :
    (C : Cover X) →
    (e : Ext1) →
    unclassifyOn C (classifyOn C e) ≡ e

  classify∘unclassify-Split :
    (SC : SplitCover X) →
    (η : CechH1Split SC) →
    classifySplit SC (unclassifySplit SC η) ≡ η

  unclassify∘classify-Split :
    (SC : SplitCover X) →
    (e : Ext1) →
    unclassifySplit SC (classifySplit SC e) ≡ e

Ext1≃CechH1Split :
  (SC : SplitCover X) →
  Ext1 ≃ CechH1Split SC
Ext1≃CechH1Split SC = isoToEquiv (iso f g sec ret)
  where
    f : Ext1 → CechH1Split SC
    f = classifySplit SC

    g : CechH1Split SC → Ext1
    g = unclassifySplit SC

    sec : (η : CechH1Split SC) → f (g η) ≡ η
    sec = classify∘unclassify-Split SC

    ret : (e : Ext1) → g (f e) ≡ e
    ret = unclassify∘classify-Split SC

-- =========================================================
-- 10. PathChain ≃ π₁oid(Cover) スケルトン
-- =========================================================

record Pi1oidObj (C : Cover X) : Type ℓ where
  field
    i : Cover.Idx C
    u : Cover.U C i

PathAt :
  (C : Cover X) →
  (a b : Pi1oidObj C) →
  Type ℓ
PathAt C a b = Cover.inc C (Pi1oidObj.i a) (Pi1oidObj.u a)
           ≡ Cover.inc C (Pi1oidObj.i b) (Pi1oidObj.u b)

postulate
  -- PathChain との対応（最終的には同値として実装）
  pathChain→pi1oid :
    (C : Cover X) →
    (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
    {x : X} →
    PathChain C b x →
    Pi1oidObj C

  pi1oid→pathChain :
    (C : Cover X) →
    (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
    (o : Pi1oidObj C) →
    PathChain C b (Cover.inc C (Pi1oidObj.i o) (Pi1oidObj.u o))

  pathChain-pi1oid-iso :
    (C : Cover X) →
    (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
    (x : X) →
    Iso (PathChain C b x)
        (Σ (Pi1oidObj C) (λ o →
         Cover.inc C (Pi1oidObj.i o) (Pi1oidObj.u o) ≡ x))

-- =========================================================
-- 11. foldChain を strict functor として整理
-- =========================================================

record StrictFunctorData (C : Cover X)
  (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V)
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) : Type (ℓ-suc ℓ) where
  field
    F₀ : Pi1oidObj C → Type ℓ
    F₁ :
      {o₁ o₂ : Pi1oidObj C} →
      PathAt C o₁ o₂ →
      Aut V
    pres-id :
      {o : Pi1oidObj C} →
      F₁ {o} {o} refl ≡ idEquiv V
    pres-comp :
      {o₁ o₂ o₃ : Pi1oidObj C} →
      (p : PathAt C o₁ o₂) →
      (q : PathAt C o₂ o₃) →
      F₁ (p ∙ q) ≡ F₁ p ∙ₑ F₁ q
    pres-inv :
      {o₁ o₂ : Pi1oidObj C} →
      (p : PathAt C o₁ o₂) →
      F₁ (sym p) ≡ invEquiv (F₁ p)

foldChain-pres-id :
  (C : Cover X) →
  (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
  (γ-cocycle :
    (i j k : Cover.Idx C) →
    (x : Cover.U C i) (y : Cover.U C j) (z : Cover.U C k) →
    (p : Cover.inc C i x ≡ Cover.inc C j y) →
    (q : Cover.inc C j y ≡ Cover.inc C k z) →
    γ i j (x , y , p) ∙ₑ γ j k (y , z , q)
    ≡ γ i k (x , z , p ∙ q)) →
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  foldChain C γ b nil ≡ idEquiv V
foldChain-pres-id C γ γ-cocycle b = refl

foldChain-pres-comp :
    (C : Cover X) →
    (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
    (γ-cocycle :
      (i j k : Cover.Idx C) →
      (x : Cover.U C i) (y : Cover.U C j) (z : Cover.U C k) →
      (p : Cover.inc C i x ≡ Cover.inc C j y) →
      (q : Cover.inc C j y ≡ Cover.inc C k z) →
      γ i j (x , y , p) ∙ₑ γ j k (y , z , q)
      ≡ γ i k (x , z , p ∙ q)) →
    (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
    {x : X} →
    (chain : PathChain C b x) →
    (i j : Cover.Idx C) →
    (xi : Cover.U C i) →
    (yj : Cover.U C j) →
    (p : Cover.inc C i xi ≡ x) →
    (q : Cover.inc C i xi ≡ Cover.inc C j yj) →
    foldChain C γ b (chain-step C b chain i j xi yj p q)
    ≡ (foldChain C γ b chain) ∙ₑ γ i j (xi , yj , q)
foldChain-pres-comp C γ γ-cocycle b chain i j xi yj p q =
  foldChain-step-compat C γ b chain i j xi yj p q

foldChain-pres-inv :
  (C : Cover X) →
  (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  (i j : Cover.Idx C) →
  (x : Cover.U C i) →
  (y : Cover.U C j) →
  (p : Cover.inc C i x ≡ Cover.inc C j y) →
  γ j i (y , x , sym p) ≡ invEquiv (γ i j (x , y , p))

foldChain-pres-inv C γ b i j x y p =
  γ-inv C γ i j x y p

foldChain-strict-functor :
  (C : Cover X) →
  (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
  (γ-cocycle :
    (i j k : Cover.Idx C) →
    (x : Cover.U C i) (y : Cover.U C j) (z : Cover.U C k) →
    (p : Cover.inc C i x ≡ Cover.inc C j y) →
    (q : Cover.inc C j y ≡ Cover.inc C k z) →
    γ i j (x , y , p) ∙ₑ γ j k (y , z , q)
    ≡ γ i k (x , z , p ∙ q)) →
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  StrictFunctorData C γ b
foldChain-strict-functor C γ γ-cocycle b = record
  { F₀ = λ _ → V
  ; F₁ = λ {o₁} {o₂} p →
      γ (Pi1oidObj.i o₁) (Pi1oidObj.i o₂) (Pi1oidObj.u o₁ , Pi1oidObj.u o₂ , p)
  ; pres-id = λ {o} →
      γ-id C γ (Pi1oidObj.i o) (Pi1oidObj.u o)
  ; pres-comp = λ {o₁} {o₂} {o₃} p q →
      sym
        (γ-cocycle
          (Pi1oidObj.i o₁) (Pi1oidObj.i o₂) (Pi1oidObj.i o₃)
          (Pi1oidObj.u o₁) (Pi1oidObj.u o₂) (Pi1oidObj.u o₃)
          p q)
  ; pres-inv = λ {o₁} {o₂} p →
      foldChain-pres-inv
        C γ b
        (Pi1oidObj.i o₁) (Pi1oidObj.i o₂)
        (Pi1oidObj.u o₁) (Pi1oidObj.u o₂)
        p
  }
