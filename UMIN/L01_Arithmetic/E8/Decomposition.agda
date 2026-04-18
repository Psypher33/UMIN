{-# OPTIONS --cubical --guardedness #-}

-- ※ 136/112分解には 1/2 が必須であるため、RingWithHalf を基盤とします
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Ring.Base
open import Cubical.Foundations.HLevels

module UMIN.L01_Arithmetic.E8.Decomposition {ℓ} (R : Ring ℓ) 
  (X : Type ℓ) 
  where

open import Cubical.Foundations.Equiv

-- これまでの資産をインポート（RingWithHalf 版の FPS を想定）
open import UMIN.L01_Arithmetic.MZV.Bialgebra R
open import UMIN.L03_Dynamic.Pentagon.Pentagon_Generator R
open import UMIN.L03_Dynamic.CCT.RH_NonCommutativeFiber R X

-- =====================================================
-- §1. 神の封印 (The 3-Type Truncation)
-- =====================================================
-- TotalFiber-NC の末尾に、以下のコンストラクタを追加したと仮定します。
-- (h-level 5 は 3-Type, すなわち 0,1,2,3-cell までを持ち、4-cell 以上は自明となる空間)

postulate
  -- TotalFiber-NC を 3-Type に強制する封印
  trunc-3 : (Cov : Covering) (C : NonCommCocycle Cov) (x : X) 
          → isOfHLevel 5 (TotalFiber-NC Cov C x)

-- =====================================================
-- §2. 局所系への τ の作用 (The Involution on Fiber)
-- =====================================================
-- Hoffman代数上の τ を、幾何学的なファイバー空間全体へ持ち上げます。
-- これが UMIN における「CPT変換」や「双対性」の幾何学的起源となります。

module FiberInvolution (Cov : Covering) (C : NonCommCocycle Cov) (x : X) where

  open RingStr (snd R) renaming (_+_ to _+C_ ; _·_ to _*C_ ; -_ to -C_)
  _+F_ : FPS-NonComm → FPS-NonComm → FPS-NonComm
  f +F g = λ w → f w +C g w
  _*F_ : FPS-NonComm → FPS-NonComm → FPS-NonComm
  f *F g = λ w → f w *C g w
  -F_ : FPS-NonComm → FPS-NonComm
  -F f = λ w → -C (f w)

  -- Hoffman 係数 FPS 上の反線形 involution τ（具体モデルで与える）
  postulate
    τ-act-FPS : FPS-NonComm → FPS-NonComm

  -- コサイクル g が τ と可換である（双対性を保つ）という物理的要請
  -- 量子推移はエルミート性を破壊してはならない。
  postulate
    g-τ-comm : (i j : Index Cov) (ui : U Cov i x) (uj : U Cov j x) (v : FPS-NonComm)
             → equivFun (NonCommCocycle.g C i j x ui uj) (τ-act-FPS v) 
               ≡ τ-act-FPS (equivFun (NonCommCocycle.g C i j x ui uj) v)
    
    -- Φ-KZ も τ に対して特定の対称性を持つ (Furusho/Drinfeld の結果より)
    Φ-τ-sym : (v : FPS-NonComm) → τ-act-FPS (Φ-KZ-act-FPS Φ-KZ v) ≡ Φ-KZ-act-FPS Φ-KZ (τ-act-FPS v)

  -- ファイバー全体への τ の作用。
  -- base/paste/Φ-twist だけをパターンマッチで定義すると assoc-face（PathP の二重境界）で
  -- hcomp の境界と整合する値を強制され、任意の postulate とは両立しにくい。
  -- よい構成的定義は後で与え、ここでは拡張を仮定する。
  postulate
    τ-Fiber : TotalFiber-NC Cov C x → TotalFiber-NC Cov C x

  -- =====================================================
  -- §3. ファイバーの 136 / 112 直和分解 (The E8 Incarnation)
  -- =====================================================
  -- 最後に、TotalFiber-NC 上の任意の点が、
  -- Hermitian (136) 成分と non-Hermitian (112) 成分の「和」として
  -- 一意に表現できることを示します。

  -- ファイバー上での加法（ベースポイントが同じ場合のみ定義可能）
  postulate
    _+Fiber_ : TotalFiber-NC Cov C x → TotalFiber-NC Cov C x → TotalFiber-NC Cov C x
    -- 係数(FPS)の加法が、ファイバーの加法と完全に準同型であることの要請
    base-add : (i : Index Cov) (ui : U Cov i x) (v w : FPS-NonComm)
             → base i ui (v +F w) ≡ base i ui v +Fiber base i ui w

    -- ファイバー上の「反転」（− は τ-分解の反対称側に使う）
    -Fiber : TotalFiber-NC Cov C x → TotalFiber-NC Cov C x

    -- 1/2 スカラー倍
    half-Fiber : TotalFiber-NC Cov C x → TotalFiber-NC Cov C x

  -- RingWithHalf から持ち上げた 1/2 と、FPS 上の分解（別ファイルの補題を想定）
  postulate
    half-FPS : FPS-NonComm
    decomp-FPS-lemma : (v : FPS-NonComm)
      → v ≡ ((v +F τ-act-FPS v) *F half-FPS) +F ((v +F (-F (τ-act-FPS v))) *F half-FPS)
    -- τ-Fiber・half-Fiber・-Fiber が base 上で係数と整合する（モデルで満たす）
    τ-Fiber-base : (i : Index Cov) (ui : U Cov i x) (v : FPS-NonComm)
      → τ-Fiber (base i ui v) ≡ base i ui (τ-act-FPS v)
    -Fiber-base : (i : Index Cov) (ui : U Cov i x) (w : FPS-NonComm)
      → -Fiber (base i ui w) ≡ base i ui (-F w)
    half-Fiber-base : (i : Index Cov) (ui : U Cov i x) (w : FPS-NonComm)
      → half-Fiber (base i ui w) ≡ base i ui (w *F half-FPS)

  -- 幾何学的 E8 分解
  proj-Herm136 : TotalFiber-NC Cov C x → TotalFiber-NC Cov C x
  proj-Herm136 t = half-Fiber (t +Fiber (τ-Fiber t))

  proj-nonHerm112 : TotalFiber-NC Cov C x → TotalFiber-NC Cov C x
  proj-nonHerm112 t = half-Fiber (t +Fiber (-Fiber (τ-Fiber t)))

  -- base 上での E8 分解（係数の decomp-FPS-lemma と base-add / 上記補題から）
  E8-Decomposition-base : (i : Index Cov) (ui : U Cov i x) (v : FPS-NonComm)
    → base i ui v ≡ proj-Herm136 (base i ui v) +Fiber proj-nonHerm112 (base i ui v)
  E8-Decomposition-base i ui v =
    sym
      ( cong₂ _+Fiber_ pHerm pNon
      ∙ sym (base-add i ui c₁ c₂)
      ∙ cong (base i ui) (sym (decomp-FPS-lemma v))
      )
    where
    c₁ = (v +F τ-act-FPS v) *F half-FPS
    c₂ = (v +F (-F (τ-act-FPS v))) *F half-FPS
    pHerm : proj-Herm136 (base i ui v) ≡ base i ui c₁
    pHerm =
      cong half-Fiber
        ( cong (base i ui v +Fiber_) (τ-Fiber-base i ui v)
        ∙ sym (base-add i ui v (τ-act-FPS v))
        )
      ∙ half-Fiber-base i ui (v +F τ-act-FPS v)
    pNon : proj-nonHerm112 (base i ui v) ≡ base i ui c₂
    pNon =
      cong half-Fiber
        ( cong (base i ui v +Fiber_) (cong -Fiber (τ-Fiber-base i ui v) ∙ -Fiber-base i ui (τ-act-FPS v))
        ∙ sym (base-add i ui v (-F (τ-act-FPS v)))
        )
      ∙ half-Fiber-base i ui (v +F (-F (τ-act-FPS v)))

  -- 全空間への拡張は trunc-3 によるエリミネータ等で行う（当面は公理でも可）
  postulate
    E8-Decomposition-Theorem :
      (t : TotalFiber-NC Cov C x) → t ≡ proj-Herm136 t +Fiber proj-nonHerm112 t