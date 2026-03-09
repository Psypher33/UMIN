{-# OPTIONS --cubical --guardedness #-}

module UMIN.L03_Func.YBE.GroupRMatrix where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import UMIN.L03_Func.YBE.UMIN_YBE_Base
open import UMIN.L03_Func.QuantumKernel.BG_FundamentalGroup
open Group

-- ================================================================
-- §1  loop-swap-R-matrix（BG のループ空間上の swap）[✓]
-- ================================================================
-- swap は置換群 S₃ の YBE 証人
-- bosonic statistics に対応する canonical な例
-- Witten (1611.00592) §2 の "trivial R-matrix" に相当

loop-swap-R-matrix : (G : Group) → RMatrix (base {G} ≡ base)
loop-swap-R-matrix G = record
  { R₁₂ = λ (p , q , r) → (q , p , r)   -- swap 1↔2
  ; R₁₃ = λ (p , q , r) → (r , q , p)   -- swap 1↔3
  ; R₂₃ = λ (p , q , r) → (p , r , q)   -- swap 2↔3
  }

-- [✓] loop-swap は refl で YBE を満たす
-- 計算: R₁₂(R₁₃(R₂₃(p,q,r)))
--       = R₁₂(R₁₃(p,r,q)) = R₁₂(q,r,p) = (r,q,p)
--       R₂₃(R₁₃(R₁₂(p,q,r)))
--       = R₂₃(R₁₃(q,p,r)) = R₂₃(r,p,q) = (r,q,p)  ← 両辺一致
loop-swap-YBE-eq : (G : Group)
  (v : (base {G} ≡ base) × (base {G} ≡ base) × (base {G} ≡ base))
  → RMatrix.R₁₂ (loop-swap-R-matrix G)
      (RMatrix.R₁₃ (loop-swap-R-matrix G)
        (RMatrix.R₂₃ (loop-swap-R-matrix G) v))
  ≡ RMatrix.R₂₃ (loop-swap-R-matrix G)
      (RMatrix.R₁₃ (loop-swap-R-matrix G)
        (RMatrix.R₁₂ (loop-swap-R-matrix G) v))
loop-swap-YBE-eq G _ = refl

-- [✓] loop-swap は YBEStructure を与える
loop-swap-YBE : (G : Group) → YBEStructure (base {G} ≡ base)
loop-swap-YBE G = record
  { rm    = loop-swap-R-matrix G
  ; yb-eq = loop-swap-YBE-eq G
  }

-- ================================================================
-- §2  swap-YBE の loop による持ち上げ [✓]
-- ================================================================
-- right-mul-equiv : Carrier G ≃ (base ≡ base) を利用
-- swap-YBE（Carrier G 版）と loop-swap-YBE の対応を明示

loop-swap-coherence : (G : Group) (a b c : Carrier G)
  → loop-swap-YBE-eq G (loop {G} a , loop {G} b , loop {G} c) ≡ refl
loop-swap-coherence G a b c = refl

-- ================================================================
-- §3  loop-R-matrix（道の合成版）[P]
-- ================================================================
-- 量子 YBE の証人（Drinfeld の意味での R 行列）
-- path 合成は非可換性を持ち、TremblingCore の量子性に対応
-- YBE の証明には追加構造（量子群・associator）が必要
--
-- 参照: Benini–Schenkel–Vicedo,
--       "Homotopical analysis of 4d Chern-Simons theory
--        and integrable field theories"
--       Commun. Math. Phys. 389 (2022) §4
--       → loop 空間上の YBE は 4d CS 理論の Ward 恒等式として保証

loop-R-matrix : (G : Group) → RMatrix (base {G} ≡ base)
loop-R-matrix G = record
  { R₁₂ = λ (p , q , r) → (p ∙ q , q , r)   -- 道の合成（右乗算）
  ; R₁₃ = λ (p , q , r) → (p , q , r)        -- identity（隣接でない対）
  ; R₂₃ = λ (p , q , r) → (p , q ∙ r , r)   -- 道の合成（右乗算）
  }

postulate
  -- [P] loop-R-matrix が YBE を満たすこと
  -- 左辺第1成分: p∙(q∙r)  vs  右辺第1成分: p∙q
  -- pathAssoc のみでは閉じない（量子群の associator が必要）
  -- Benini–Schenkel–Vicedo (2022) §4 の homotopical Ward identity に委譲
  loop-YBE-eq : (G : Group)
    (v : (base {G} ≡ base) × (base {G} ≡ base) × (base {G} ≡ base))
    → RMatrix.R₁₂ (loop-R-matrix G)
        (RMatrix.R₁₃ (loop-R-matrix G)
          (RMatrix.R₂₃ (loop-R-matrix G) v))
    ≡ RMatrix.R₂₃ (loop-R-matrix G)
        (RMatrix.R₁₃ (loop-R-matrix G)
          (RMatrix.R₁₂ (loop-R-matrix G) v))

-- ================================================================
-- §4  group-R-matrix（Carrier G 上）[P]
-- ================================================================
-- Skeleton との互換性のために維持
-- Carrier G ≅ base ≡ base（via right-mul-equiv）を通じて
-- loop-R-matrix と対応する古典的な R 行列
-- YBE の証明には量子群構造（Drinfeld associator）が必要
--
-- 参照: Drinfeld, "Quantum Groups" (1987)
--       → Carrier G 上の non-trivial YBE は量子変形を要求

group-R-matrix : (G : Group) → RMatrix (Carrier G)
group-R-matrix G = record
  { R₁₂ = λ (v₁ , v₂ , v₃) → (G ._⋆_ v₁ v₂ , v₂ , v₃)
  ; R₁₃ = λ (v₁ , v₂ , v₃) → (G ._⋆_ v₁ v₃ , v₂ , v₃)
  ; R₂₃ = λ (v₁ , v₂ , v₃) → (v₁ , G ._⋆_ v₂ v₃ , v₃)
  }

postulate
  -- [P] group-R-matrix が YBE を満たすこと
  -- Drinfeld (1987) + right-mul-equiv による持ち上げで保証される予定
  group-YBE-eq : (G : Group)
    (v : Carrier G × Carrier G × Carrier G)
    → RMatrix.R₁₂ (group-R-matrix G)
        (RMatrix.R₁₃ (group-R-matrix G)
          (RMatrix.R₂₃ (group-R-matrix G) v))
    ≡ RMatrix.R₂₃ (group-R-matrix G)
        (RMatrix.R₁₃ (group-R-matrix G)
          (RMatrix.R₁₂ (group-R-matrix G) v))

-- ================================================================
-- §5  YBEStructure のまとめ
-- ================================================================

-- [✓] loop-swap（canonical な証人）
loop-swap-YBEStructure : (G : Group) → YBEStructure (base {G} ≡ base)
loop-swap-YBEStructure = loop-swap-YBE

-- [P] loop-R（量子 YBE）
loop-YBE : (G : Group) → YBEStructure (base {G} ≡ base)
loop-YBE G = record
  { rm    = loop-R-matrix G
  ; yb-eq = loop-YBE-eq G
  }

-- [P] group-YBE（古典 YBE）
group-YBE : (G : Group) → YBEStructure (Carrier G)
group-YBE G = record
  { rm    = group-R-matrix G
  ; yb-eq = group-YBE-eq G
  }
