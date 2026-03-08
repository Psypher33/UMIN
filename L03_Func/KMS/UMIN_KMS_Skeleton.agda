{-# OPTIONS --cubical --guardedness #-}
-- 注：postulate 使用のため --safe は付けない（骨格・コンパイル通過版）

-- ================================================================
--  L03_Func/KMS/UMIN_KMS_Skeleton.agda
--  定理 B：KMS 条件 = 随伴欠陥から創発
--  全骨格（postulate 優先・コンパイル通過版）
-- ================================================================

module UMIN.L03_Func.KMS.UMIN_KMS_Skeleton where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Int.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import UMIN.L00_Core.Axiom.TremblingCore
open import UMIN.L03_Func.QuantumKernel.PhaseC_Bridge

-- ================================================================
-- §1  モジュラーフロー [✓ 型定義]
-- ================================================================

record ModularFlow (A : Type) : Type₁ where
  field
    σ      : ℤ → A ≃ A
    -- [P] σ₀ = id（Tomita–Takesaki から）
    σ-zero : σ (pos 0) ≡ idEquiv A

-- ================================================================
-- §2  KMS 経路の型 [✓]
-- ================================================================

-- kms : s(s†(a)) =_A σ_{β}(a)
record KMSPath
  (tc : TremblingCore)
  (A  : Type)
  (sc : SasakiConn tc A)
  (fl : ModularFlow A)
  (β  : ℤ)
  : Type where
  open SasakiConn sc
  open ModularFlow fl
  field
    -- ★ 定理 B の核心：随伴欠陥 → モジュラーフロー
    kms       : (a : A) → s (s† a) ≡ equivFun (σ β) a
    -- 非可縮性：Ext¹ ≠ 0 のとき kms は定数道でない
    -- （refl は s(s†a)=equivFun(σ β)a の定義的等値が必要なため、
    --  「∀ i → kms a i ≡ equivFun (σ β) a」で自明道を表す）
    -- [P] → KMSNonTriviality.agda で証明
    kms-non-triv : (a : A) → (∀ i → kms a i ≡ equivFun (σ β) a) → β ≡ pos 0 → ⊥

-- 詳細釣り合い条件の型 [✓]
DetailedBalance :
  {tc : TremblingCore} {A : Type}
  → SasakiConn tc A → ModularFlow A → ℤ → Type
DetailedBalance {_} {A} sc fl β =
  (a b : A) →
  SasakiConn.s sc (SasakiConn.s† sc a) ≡
  equivFun (ModularFlow.σ fl β) a

-- ================================================================
-- §3  定理 B のpostulate群 [P]
-- ================================================================

postulate
  -- [P] モジュラーフローの存在（Ext¹ ≠ 0 から）
  -- 参照：Takesaki "Tomita's Theory" Lect.Notes Math.128 (1970)
  ext1-gives-flow :
    (tc : TremblingCore) (A : Type)
    (sc : SasakiConn tc A)
    → ModularFlow A

  -- [P] 逆温度 β の存在（ΩA のループ巻き数）
  -- 参照：Scandi–Alhambra PRL (2024)
  ext1-gives-beta :
    (tc : TremblingCore) (A : Type)
    (sc : SasakiConn tc A)
    → ℤ

  -- [P] KMS 経路の構成
  -- 橋渡し：Yoneda（導来圏版）+ transport
  ext1-gives-kms :
    (tc : TremblingCore) (A : Type)
    (sc : SasakiConn tc A)
    → KMSPath tc A sc
        (ext1-gives-flow tc A sc)
        (ext1-gives-beta tc A sc)

-- ================================================================
-- §4  定理 B（型シグネチャ + postulate 証明）[✓ 型]
-- ================================================================

TheoremB-Type : TremblingCore → Type₁
TheoremB-Type tc =
  (A : Type) (sc : SasakiConn tc A)
  → Σ[ fl ∈ ModularFlow A ]
    Σ[ β ∈ ℤ ]
    KMSPath tc A sc fl β

-- 定理 B の証明（postulate への委譲）
theorem-B : (tc : TremblingCore) → TheoremB-Type tc
theorem-B tc A sc =
  ( ext1-gives-flow tc A sc
  , ext1-gives-beta tc A sc
  , ext1-gives-kms  tc A sc
  )

-- ================================================================
-- §5  完全随伴 → KMS は refl（ゼロ点の静寂の KMS 版）[✓]
-- ================================================================

perfect-kms-refl :
  {tc : TremblingCore} {A : Type}
  (sc : SasakiConn tc A)
  → Perfect sc
  → (a : A) →
    SasakiConn.s sc (SasakiConn.s† sc a) ≡ a
perfect-kms-refl sc perf a = perf a
-- ↑ Perfect の定義そのもの：refl 相当 [✓]

-- ================================================================
-- §6  Settimo et al. との接続の型 [✓]
-- ================================================================

-- L_t ≠ R_t の型論的捕捉
record SchrodingerHeisenbergGap
  (tc : TremblingCore) (A : Type)
  (sc : SasakiConn tc A) : Type₁ where
  open SasakiConn sc
  field
    -- Schrödinger 側：完全随伴なら分解可能
    schrodinger-CP  : Perfect sc → Type
    -- Heisenberg 側：独立な概念
    heisenberg-nonP : Σ[ a ∈ A ] (s (s† a) ≡ a) → Type
    -- 非同値性の型証人
    gap-witness :
      (perf : Perfect sc)
      → schrodinger-CP perf
      → Σ[ a ∈ A ]
          (s (s† a) ≡ a) × (heisenberg-nonP (a , perf a) → Type)

-- ================================================================
-- §7  検証状況サマリー
-- ================================================================
--
-- [✓] ModularFlow（型）, KMSPath（型）, DetailedBalance（型）
-- [✓] TheoremB-Type（型）
-- [✓] theorem-B（ext1-gives-* への委譲で構造上 [✓]）
-- [✓] perfect-kms-refl（Perfect の定義から直接）
-- [✓] SchrodingerHeisenbergGap（型）
--
-- [P] ext1-gives-flow（Takesaki 1970 + 圏論的輸送）
-- [P] ext1-gives-beta（π₁(ΩA) ≅ ℤ の生成元）
-- [P] ext1-gives-kms （Yoneda 導来圏版）
-- [P] ModularFlow.σ-zero（σ₀ = id）
-- [P] KMSPath.kms-non-triv（非可縮性）
--
-- 次の実装ターゲット：
--   L03_Func/KMS/KMSNonTriviality.agda
--   → PhaseC_Bridge の UniversalCover を使って
--     kms-non-triv を [✓] に格上げ
-- ================================================================
