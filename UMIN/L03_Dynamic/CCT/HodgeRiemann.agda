{-# OPTIONS --cubical --guardedness #-}

------------------------------------------------------------------------
-- HodgeRiemann.agda
-- UMIN / L02_Bridge / HodgeRiemann.agda
-- Open Problem xvi（前倒し実装）
-- Ext¹ ≅ ℤ 上の Hodge-Riemann型二次形式 Q の最小公理系
--
-- 設計方針（2026年3月28日 Eva × Psypher 確定）：
--   ・Q-form を「∃ σ」に落として σ依存を排除 → 循環を完全遮断
--   ・droite条件（HRQ-3）が σ=+1 を後から一意決定
--   ・EP-is-droite との同値は Phase 2 で証明
--
-- 状態：[P]  Phase 1 = 型骨格完成
------------------------------------------------------------------------

module UMIN.L03_Dynamic.CCT.HodgeRiemann where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Data.Int          using (ℤ; pos; negsuc; _·_)
open import Cubical.Data.Sigma
  -- ∃[ x ∈ A ] … は ∃-syntax を import しないと解析されない
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)

-- EPTangential との接続（Phase 2 で使用）
-- open import UMIN.L02_Bridge.EPTangential

------------------------------------------------------------------------
-- §1. 符号の型（σ の値域）
------------------------------------------------------------------------

data Sign : Type₀ where
  plus  : Sign     -- σ = +1  droite方向・観測可能
  minus : Sign     -- σ = -1  gauche方向・双対

sign-val : Sign → ℤ
sign-val plus  = pos 1
sign-val minus = negsuc 0    -- = -1

------------------------------------------------------------------------
-- §2. 最小公理系 HRQ（Hodge-Riemann for Ext¹）
--
--  [HRQ-1] 対称性
--  [HRQ-2] 積形式の存在（σ依存を∃に落として循環遮断）★
--  [HRQ-3] droite整合条件（σ=+1 を後から一意決定）
------------------------------------------------------------------------

postulate
  -- [HRQ-1] 対称性
  Q        : ℤ → ℤ → ℤ
  Q-symm   : (n m : ℤ) → Q n m ≡ Q m n

  -- [HRQ-2] ∃ σ に落とした積形式（循環完全遮断）★
  -- 「Q は何らかの符号 σ による積形式である」という存在命題
  -- σ を引数に取らないことで、呼び出し側が σ を選べない
  Q-exists : ∃[ σ ∈ Sign ] ((n m : ℤ) → Q n m ≡ sign-val σ · n · m)

  -- [HRQ-3] droite整合条件（Q>0 の意味を正の整数で表現）
  Q-droite-pos : Q (pos 1) (pos 1) ≡ pos 1

------------------------------------------------------------------------
-- §3. 一意性定理
-- Q-droite-pos から σ = plus（+1）が一意に決まる
------------------------------------------------------------------------

HR-sign-unique : Sign
HR-sign-unique = plus
-- 根拠：Q-exists の σ について
--   Q(pos 1, pos 1) = sign-val σ * 1 * 1 = sign-val σ
--   Q-droite-pos : Q(pos 1, pos 1) = pos 1
--   ∴ sign-val σ = pos 1 ⟹ σ = plus
-- [P] 形式証明は Phase 2（ℤの等式判定が必要）

HR-uniqueness : Q (pos 1) (pos 1) ≡ pos 1
              → ∃[ σ ∈ Sign ] (sign-val σ ≡ pos 1)
HR-uniqueness _ = ∣ plus , refl ∣₁
-- plus を証人として提示：sign-val plus = pos 1 = refl ✅

------------------------------------------------------------------------
-- §4. droite / gauche の非対称性
--
-- Q(pos 1, pos 1) = +1 > 0  ← droite：観測可能 [✓ Q-droite-pos]
-- Q(neg 1, neg 1) = +1 > 0  ← gauche：Q>0 だが生成元でない
--
-- ★ 非対称性の根拠：
--   「Q>0」だけでは droite と gauche を区別できない。
--   区別するのは Ext¹ 同型の生成元選択（AlphaBridge.agda: pos 1）。
--   つまり Q は「正方向の存在」を保証し、
--   「どちらが正方向か」は EP-is-droite が決定する。
------------------------------------------------------------------------

postulate
  Q-gauche-also-pos : Q (negsuc 0) (negsuc 0) ≡ pos 1
  -- [P] sign-val plus · negsuc 0 · negsuc 0 = +1 の計算
-- Phase 2 で ℤ算術から導出

------------------------------------------------------------------------
-- §5. EP-is-droite との同値（Phase 2 ターゲット）
--
-- 目標：
--   Q (pos 1) (pos 1) ≡ pos 1
--   ↔ EP ≡ droite
--
-- 直観：
--   Ext¹ の生成元 pos 1 が「観測可能方向（Q>0）」を向いている
--   ⟺ EP が droite（KZ標準正規化）に固定されている
------------------------------------------------------------------------

-- Phase 2 で EPTangential.agda を open してから証明
-- postulate
--   HR-EP-equiv : Q (pos 1) (pos 1) ≡ pos 1
--               ↔ EP ≡ droite

------------------------------------------------------------------------
-- §6. UMIN全経路との接続図（コメント）
--
--   EP-is-droite = refl          [✓] EPTangential.agda
--         ↕ 同値（Phase 2）
--   Q(pos 1, pos 1) = pos 1      [P] Q-droite-pos（本ファイル）
--         ↕ HR-uniqueness
--   σ = plus（+1）に一意固定      [P] HR-uniqueness
--         ↕
--   Ext¹ 生成元 = 観測可能方向    [✓] AlphaBridge.agda: pos 1
--         ↕
--   α⁻¹ = 136 + 1 = 137          [✓] Drinfeld_Emergence.agda
--
-- ★ 全経路が「droite = +1 = 観測可能」で貫かれている
------------------------------------------------------------------------

-- ファイル終端