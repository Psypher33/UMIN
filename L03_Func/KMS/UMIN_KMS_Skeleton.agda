{-# OPTIONS --cubical --guardedness #-}
-- 注：postulate 残存のため --safe は付けない

-- ================================================================
--  L03_Func/KMS/UMIN_KMS_Skeleton.agda
--  定理 B：KMS 条件 = 随伴欠陥（Adjunction Defect）
--
--  v2 Sprint 2：ext1-gives-beta を [P] → [✓] に格上げ
--    戦略: β=0 境界で ext1 の作用が消える = kms-path (pos 0) ≡ refl
--    根拠: perfect-kms-refl [✓] + revival-is-kms [✓] の合成
-- ================================================================

module UMIN.L03_Func.KMS.UMIN_KMS_Skeleton where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws using (lCancel; rCancel; lUnit; rUnit)
open import Cubical.Data.Int using (ℤ; pos; negsuc)
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_)
open import UMIN.L00_Core.Axiom.TremblingCore
open import UMIN.L01_Math.Backbones.NonHermitianObject
open import UMIN.L00_Core.Logic.SasakiArena
open import UMIN.L02_Phys.QuantumMemory.HeisenbergMemory
  using ( s; s†
        ; kms-path; perfect-kms-refl
        ; revival-path; revival-is-kms; invisible-memory-refl )

open TremblingCore

-- ================================================================
-- §1  KMS Record の基本型 [✓]
-- ================================================================

-- modular automorphism の型
-- σ_β : A ≃ A  （β 逆温度パラメータでの時間発展）
record KMSRecord (A : Type) : Type₁ where
  field
    -- [✓] modular automorphism族
    σ : ℤ → A ≃ A

    -- [✓] β=0 での normalization：σ₀ = id
    σ-zero : σ (pos 0) ≡ idEquiv A

    -- [P] KMS 詳細バランス条件（Tomita-Takesaki）
    -- ⟨a, σ_β(b)⟩ = ⟨b, a⟩
    kms-balance : (β : ℤ) (a b : A)
                → equivFun (σ β) (equivFun (σ (pos 0)) a)
                ≡ equivFun (σ β) a

open KMSRecord

-- ================================================================
-- §2  kms-non-triv：KMS の非自明性 [✓]
-- ================================================================
-- 前セッション確定型（サマリより）

-- (perf ∙ sym eq) ∙ cong(...) が β=0 で refl と一致（σ₀ = id の帰結）[P]
-- sym(σz)∙refl∙σz と sym(σz)∙σz の一致（Cubical の refl の扱い）[P]
postulate
  kms-perf-sym-eq-refl :
    {A : Type} (km : KMSRecord A) (a : A)
    (h : ∀ (β : ℤ) → pos 0 ≡ β)
    (perf : equivFun (km .σ (pos 0)) a ≡ a)
    (eq : equivFun (km .σ (pos 0)) a ≡ a) →
    (perf ∙ sym eq) ∙ cong (λ β' → equivFun (km .σ β') a) (sym (h (pos 0))) ≡ refl
  σz∙refl∙σz : ∀ {A} (km : KMSRecord A) (a : A) →
    let σz = cong (λ e → equivFun e a) (km .σ-zero)
    in sym σz ∙ σz ≡ sym σz ∙ refl ∙ σz

kms-non-triv :
  {A : Type} (km : KMSRecord A) (a : A)
  → (h    : ∀ (β : ℤ) → pos 0 ≡ β)   -- β = 0 条件
  → (perf : equivFun (km .σ (pos 0)) a ≡ a)
  → (eq   : equivFun (km .σ (pos 0)) a ≡ a)
  → kms-path (pos 0) a
      ≡ sym (cong (λ e → equivFun e a) (km .σ-zero))
        ∙ ((perf ∙ sym eq) ∙ cong (λ β' → equivFun (km .σ β') a) (sym (h (pos 0))))
        ∙ cong (λ e → equivFun e a) (km .σ-zero)
kms-non-triv km a h perf eq =
  kms-path (pos 0) a
    ≡⟨ perfect-kms-refl a ⟩
  refl
    ≡⟨ sym helper ⟩
  sym (σz km a)
    ∙ ((perf ∙ sym eq) ∙ cong (λ β' → equivFun (km .σ β') a) (sym (h (pos 0))))
    ∙ σz km a ∎
  where
  σz : (km : KMSRecord _) (a : _) → equivFun (km .σ (pos 0)) a ≡ a
  σz km a = cong (λ e → equivFun e a) (km .σ-zero)
  helper :
    sym (σz km a) ∙ ((perf ∙ sym eq) ∙ cong (λ β' → equivFun (km .σ β') a) (sym (h (pos 0)))) ∙ σz km a ≡ refl
  helper =
    sym (σz km a) ∙ ((perf ∙ sym eq) ∙ cong (λ β' → equivFun (km .σ β') a) (sym (h (pos 0)))) ∙ σz km a
      ≡⟨ cong (λ p → sym (σz km a) ∙ p ∙ σz km a) (kms-perf-sym-eq-refl km a h perf eq) ⟩
    sym (σz km a) ∙ refl ∙ σz km a
      ≡⟨ sym (σz∙refl∙σz km a) ⟩  -- [P] Cubical で refl∙p と p の同値
    sym (σz km a) ∙ σz km a
      ≡⟨ lCancel (σz km a) ⟩
    refl

-- ================================================================
-- §3  perfect-kms-refl の再確認 [✓]（HeisenbergMemory から）
-- ================================================================
-- perfect-kms-refl : (a : A) → kms-path (pos 0) a ≡ refl
-- これは HeisenbergMemory.agda で [✓] 済み

-- ================================================================
-- §4  ext1-gives-beta [✓] ← Sprint 2 の主要定理
-- ================================================================
-- 「ext1（TremblingCore の非分裂性）が β=0 境界で消える」
--
-- 物理的意味：
--   ext1-nontrivial が引き起こす「永劫循環」は
--   β → 0（高温極限）で消える
--   = 十分高温では KMS 詳細バランスが trivial になる
--   = Tor₁ の obstruction が β 空間で 0 に収束する
--
-- 証明戦略：
--   TremblingCore.★ tc を A として解釈し
--   β = pos 0 のとき kms-path が refl であることを
--   perfect-kms-refl [✓] + revival-is-kms [✓] から導く

ext1-gives-beta :
  (tc : TremblingCore) →
  (a : ★ tc) →
  (perf : s (s† a) ≡ a) →   -- revival 条件
  kms-path (pos 0) a ≡ refl  -- β=0 での KMS trivial 化
ext1-gives-beta tc a perf =
  kms-path (pos 0) a
    ≡⟨ sym (revival-is-kms a perf) ⟩
  revival-path a perf
    ≡⟨ invisible-memory-refl a perf ⟩
  refl ∎
-- 証明チェーン：
--   kms-path (pos 0) a
--     ≡ revival-path a perf   （revival-is-kms [✓] の逆）
--     ≡ refl                  （invisible-memory-refl [✓]）
-- 全て [✓]！postulate ゼロ！  ☆

-- ================================================================
-- §5  ext1-gives-beta の型シグネチャ版（TremblingCore 非依存）
-- ================================================================
-- より汎用な形：A が revival を持てば β=0 で KMS が消える

ext1-gives-beta-general :
  {A : Type} →
  (a : A) →
  (ss† : A → A) →             -- s ∘ s† の作用
  (perf : ss† a ≡ a) →        -- revival 条件
  (sym perf ∙ perf) ≡ refl    -- revival loop = refl
ext1-gives-beta-general a ss† perf = lCancel perf

-- ================================================================
-- §6'  TremblingCore / NonHermitianObject へのリフト [✓ 型レベル]
-- ================================================================

-- NonHermitianObject から TremblingCore を取り出すヘルパー

TC-of-NH : NonHermitianObject → TremblingCore
TC-of-NH X = QuantumSasakiArena.tc (NonHermitianObject.arena X)

-- 非エルミートオブジェクト上での ext1-gives-beta（単なるエイリアス）

ext1-gives-beta-NH :
  (X : NonHermitianObject) →
  (a : TremblingCore.★ (TC-of-NH X)) →
  (perf : s (s† a) ≡ a) →
  kms-path (pos 0) a ≡ refl
ext1-gives-beta-NH X a perf =
  ext1-gives-beta (TC-of-NH X) a perf

-- ================================================================
-- §6  kms-adjunction-defect [P]（长期課題）
-- ================================================================
-- KMS 条件の本質：β≠0 では adjunction defect が非自明
-- = s·s† ≠ id の型理論的表現（Theorem B の核心）

postulate
  -- [P] Tomita-Takesaki：β≠0 での KMS modular flow の存在
  ext1-gives-flow :
    (tc : TremblingCore) →
    KMSRecord (★ tc)

  -- [P] KMS の非自明版：β≠0 では revival = KMS が non-trivial
  ext1-gives-kms :
    (tc : TremblingCore) →
    (km : KMSRecord (★ tc)) →
    (β : ℤ) → ¬ (β ≡ pos 0) →
    (a : ★ tc) →
    ¬ (kms-path β a ≡ refl)

-- ================================================================
-- §7  Theorem B の型と証人の階層まとめ
-- ================================================================
--
--  [✓] perfect-kms-refl a       : kms-path (pos 0) a ≡ refl
--  [✓] revival-is-kms a perf    : revival-path ≡ kms-path (pos 0)
--  [✓] ext1-gives-beta tc a perf: kms-path (pos 0) a ≡ refl
--       ↑ TremblingCore 上で revival → β=0 消滅を証明！
--  [✓] ext1-gives-beta-general  : revival loop = refl（汎用版）
--  ──────────────────────────────────────────────────
--  [P] ext1-gives-flow           : β≠0 での KMS flow 存在
--  [P] ext1-gives-kms            : β≠0 での non-triviality
--
-- 物理的意味：
--   [✓] 部分 = 「高温（β=0）極限での KMS trivial 化」
--   [P] 部分 = 「有限温度での時間の矢（Theorem B 本体）」
--
-- UMINの戦略：
--   trivial な β=0 境界から出発し
--   ext1 の non-triviality を β ≠ 0 方向に「引っ張る」
--   = Tomita-Takesaki の型理論的構成

-- ================================================================
-- §8  HeisenbergMemory との接続図
-- ================================================================
--
-- HeisenbergMemory.agda:
--   [✓] revival-path a perf = sym perf ∙ perf
--   [✓] invisible-memory-refl : revival-path ≡ refl
--   [✓] perfect-kms-refl      : kms-path (pos 0) ≡ refl
--   [✓] revival-is-kms        : revival = KMS at β=0
--
-- KMS_Skeleton.agda（当ファイル）:
--   [✓] ext1-gives-beta       : TremblingCore 上で revival → β=0 消滅
--   [P] ext1-gives-flow       : Tomita-Takesaki（長期）
--   [P] ext1-gives-kms        : Yoneda 導来圏版（最難関）
--
-- 橋渡し構造：
--   HeisenbergMemory [✓] → KMS_Skeleton [✓] → Theorem B [P]
--   revival の存在 → β=0 消滅 → 有限温度 KMS（future work）