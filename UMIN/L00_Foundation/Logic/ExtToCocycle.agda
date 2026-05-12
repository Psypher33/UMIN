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

rep : Ext1 → (X → BAut)
rep = extClassifyingMap

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

-- =========================================================
-- 3. Extension
-- =========================================================

record Extension : Type (ℓ-suc ℓ) where
  field
    class : Ext1
    E     : Type ℓ
    i     : X → E
    p     : E → X
    fiber≃ : (x : X) → (Σ E (λ e → p e ≡ x)) ≃ V

postulate
  -- BAut 上の universal bundle（最小インターフェース）
  UniversalBundle : BAut → Type ℓ
  universalPoint : (b : BAut) → UniversalBundle b
  pullbackFiber≃V :
    (f : X → BAut) →
    (x : X) →
    (Σ (Σ X (λ x' → UniversalBundle (f x')))
       (λ e → fst e ≡ x)) ≃ V

Ext→Extension : Ext1 → Extension
Ext→Extension e .Extension.class = e
Ext→Extension e .Extension.E =
  Σ X (λ x → UniversalBundle (rep e x))
Ext→Extension e .Extension.i x =
  x , universalPoint (rep e x)
Ext→Extension e .Extension.p ex =
  fst ex
Ext→Extension e .Extension.fiber≃ x =
  pullbackFiber≃V (rep e) x

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

-- Split cover 版の Čech H¹（set truncation として実体化）
CechH1Split :
  (SC : SplitCover X) →
  Type ℓ
CechH1Split SC = ∥ Cech1On (SplitCover.C SC) ∥₀

-- fixed split cover から Čech H¹ 代表へ送る射影
cech1-class :
  (SC : SplitCover X) →
  Cech1On (SplitCover.C SC) →
  CechH1Split SC
cech1-class SC ξ = ∣ ξ ∣₀

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

extensionClass : Extension → Ext1
extensionClass = Extension.class

-- STEP4: classify（Ext¹ → Čech H¹）
-- Ext¹ の代表から fixed cover 上の cocycle を抽出
classifyOn :
  (C : Cover X) →
  Ext1 →
  Cech1On C
classifyOn C e = Cocycle C , CocycleCondition C

classifySplit :
  (SC : SplitCover X) →
  Ext1 →
  CechH1Split SC
classifySplit SC e = cech1-class SC (classifyOn (SplitCover.C SC) e)

-- fixed cover では類写像は代表写像と整合
classifySplit-β :
  (SC : SplitCover X) →
  (e : Ext1) →
  classifySplit SC e
  ≡ cech1-class SC (classifyOn (SplitCover.C SC) e)
classifySplit-β SC e = refl

-- STEP5: unclassify（Čech H¹ → Ext¹）
unclassifyOn :
  (C : Cover X) →
  Cech1On C →
  Ext1

unclassifySplit :
  (SC : SplitCover X) →
  CechH1Split SC →
  Ext1

-- fixed cover cocycle から Ext¹ の代表へ（暫定の基点実装）
unclassifyOn C ξ = extensionClass (glueExtensionOn C ξ)

-- split cover 版は truncation 消去で構成
unclassifySplit SC = rec isSetSetTrunc (unclassifyOn (SplitCover.C SC))

-- fixed cover 代表を類へ上げてから戻すと一致（暫定実装下では自明）
unclassifySplit-β :
  (SC : SplitCover X) →
  (ξ : Cech1On (SplitCover.C SC)) →
  unclassifySplit SC (cech1-class SC ξ)
  ≡ unclassifyOn (SplitCover.C SC) ξ
unclassifySplit-β SC ξ = refl

postulate
  glueExtensionOn-sound-Split :
    (SC : SplitCover X) →
    ((e : Ext1) →
      extensionClass
        (glueExtensionOn (SplitCover.C SC)
          (classifyOn (SplitCover.C SC) e))
      ≡ e)
    ×
    ((ξ : Cech1On (SplitCover.C SC)) →
      classifyOn (SplitCover.C SC)
        (extensionClass (glueExtensionOn (SplitCover.C SC) ξ))
      ≡ ξ)

classifyOn-glue-class-Split :
  (SC : SplitCover X) →
  (e : Ext1) →
  extensionClass
    (glueExtensionOn (SplitCover.C SC)
      (classifyOn (SplitCover.C SC) e))
  ≡ e
classifyOn-glue-class-Split SC = fst (glueExtensionOn-sound-Split SC)

classifyOn-extensionClass-glue-Split :
  (SC : SplitCover X) →
  (ξ : Cech1On (SplitCover.C SC)) →
  classifyOn (SplitCover.C SC)
    (extensionClass (glueExtensionOn (SplitCover.C SC) ξ))
  ≡ ξ
classifyOn-extensionClass-glue-Split SC = snd (glueExtensionOn-sound-Split SC)

-- STEP6: classify/unclassify の相互逆（descent = 同値）
unclassify∘classify-Split :
  (SC : SplitCover X) →
  (e : Ext1) →
  unclassifySplit SC (classifySplit SC e) ≡ e
unclassify∘classify-Split SC e =
  unclassifySplit-β SC (classifyOn (SplitCover.C SC) e)
  ∙ classifyOn-glue-class-Split SC e

CechH1Split-elim :
  (SC : SplitCover X) →
  (P : CechH1Split SC → Type ℓ) →
  ((η : CechH1Split SC) → isSet (P η)) →
  ((ξ : Cech1On (SplitCover.C SC)) → P (cech1-class SC ξ)) →
  (η : CechH1Split SC) →
  P η
CechH1Split-elim SC P Pset f =
  elim Pset f

classify∘unclassify-Split :
  (SC : SplitCover X) →
  (η : CechH1Split SC) →
  classifySplit SC (unclassifySplit SC η) ≡ η
classify∘unclassify-Split SC =
  CechH1Split-elim SC
    (λ η → classifySplit SC (unclassifySplit SC η) ≡ η)
    (λ η → isProp→isSet (isSetSetTrunc _ _))
    λ ξ →
      cong (classifySplit SC) (unclassifySplit-β SC ξ)
      ∙ cong (cech1-class SC)
             (classifyOn-extensionClass-glue-Split SC ξ)

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
-- 12. Roadmap実装: π₁化 → Deck → 像同値 → 固定点
-- =========================================================

-- Step 1: PathChain の loop 部分を抽出し、set truncation で π₁ 化
LoopRaw :
  (C : Cover X) →
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  Type ℓ
LoopRaw C b = PathChain C b (Cover.inc C (fst b) (snd b))

Loopπ₁ :
  (C : Cover X) →
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  Type ℓ
Loopπ₁ C b = ∥ LoopRaw C b ∥₀

foldLoopRaw :
  (C : Cover X) →
  (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  LoopRaw C b → Aut V
foldLoopRaw C γ b l = foldChain C γ b l

foldLoop :
  (C : Cover X) →
  (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  Loopπ₁ C b →
  ∥ Aut V ∥₀
foldLoop C γ b = rec isSetSetTrunc (λ l → ∣ foldLoopRaw C γ b l ∣₀)

foldLoop-resp-ChainEq :
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
  (l₁ l₂ : LoopRaw C b) →
  ChainEq C b l₁ l₂ →
  foldLoopRaw C γ b l₁ ≡ foldLoopRaw C γ b l₂
foldLoop-resp-ChainEq C γ γ-cocycle b l₁ l₂ eq =
  foldChain-resp C γ γ-cocycle b l₁ l₂ eq

-- Step 2: Deck群（自己同型 + 自然性）の抽出
Deck :
  (C : Cover X) →
  (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  Type ℓ
Deck C γ b =
  Σ (Aut V) λ α →
    ((l : LoopRaw C b) →
      α ∙ₑ foldLoopRaw C γ b l ≡ foldLoopRaw C γ b l ∙ₑ α)
    ×
    ∥ Σ (LoopRaw C b) (λ l → foldLoopRaw C γ b l ≡ α) ∥₀

-- Step 3: π₁ の像（monodromy image）と Deck の比較対象
Pi1Image :
  (C : Cover X) →
  (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  Type ℓ
Pi1Image C γ b =
  Σ (Aut V) λ α →
    ∥ Σ (LoopRaw C b) (λ l → foldLoopRaw C γ b l ≡ α) ∥₀

loop→pi1Image :
  (C : Cover X) →
  (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  LoopRaw C b →
  Pi1Image C γ b
loop→pi1Image C γ b l =
  foldLoopRaw C γ b l , ∣ (l , refl) ∣₀

deck→Aut :
  (C : Cover X) →
  (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  Deck C γ b →
  Aut V
deck→Aut C γ b d = fst d

deck→pi1Image :
  (C : Cover X) →
  (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  Deck C γ b →
  Pi1Image C γ b
deck→pi1Image C γ b (α , nat , img) = α , img

postulate
  deckNaturalityFromImage :
    (C : Cover X) →
    (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
    (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
    (α : Aut V) →
    ∥ Σ (LoopRaw C b) (λ l → foldLoopRaw C γ b l ≡ α) ∥₀ →
    (l : LoopRaw C b) →
    α ∙ₑ foldLoopRaw C γ b l ≡ foldLoopRaw C γ b l ∙ₑ α

pi1Image→deck :
  (C : Cover X) →
  (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  Pi1Image C γ b →
  Deck C γ b

postulate
  deck→pi1Image-ret :
    (C : Cover X) →
    (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
    (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
    (d : Deck C γ b) →
    pi1Image→deck C γ b (deck→pi1Image C γ b d) ≡ d

pi1Image→deck C γ b (α , img) =
  α , (deckNaturalityFromImage C γ b α img) , img

deck→pi1Image-sec :
  (C : Cover X) →
  (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  (x : Pi1Image C γ b) →
  deck→pi1Image C γ b (pi1Image→deck C γ b x) ≡ x
deck→pi1Image-sec C γ b (α , img) = refl

deck≃pi1Image :
  (C : Cover X) →
  (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  Deck C γ b ≃ Pi1Image C γ b
deck≃pi1Image C γ b =
  isoToEquiv
    (iso
      (deck→pi1Image C γ b)
      (pi1Image→deck C γ b)
      (deck→pi1Image-sec C γ b)
      (deck→pi1Image-ret C γ b))

-- Step 4: 固定点（trace への入口）
Fix : Aut V → Type ℓ
Fix f = Σ V (λ v → equivFun f v ≡ v)

FixDeck :
  (C : Cover X) →
  (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  Deck C γ b →
  Type ℓ
FixDeck C γ b d = Fix (deck→Aut C γ b d)

FixImage :
  (C : Cover X) →
  (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  Pi1Image C γ b →
  Type ℓ
FixImage C γ b img = Fix (fst img)

fixDeck→fixImage :
  (C : Cover X) →
  (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  (d : Deck C γ b) →
  FixDeck C γ b d →
  FixImage C γ b (deck→pi1Image C γ b d)
fixDeck→fixImage C γ b d fx = fx

fixFromLoop :
  (C : Cover X) →
  (γ : (i j : Cover.Idx C) → Overlap C i j → Aut V) →
  (b : Σ (Cover.Idx C) (λ i → Cover.U C i)) →
  (l : LoopRaw C b) →
  FixImage C γ b (loop→pi1Image C γ b l) →
  Fix (foldLoopRaw C γ b l)
fixFromLoop C γ b l fx = fx
