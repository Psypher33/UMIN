{-# OPTIONS --cubical --safe --guardedness #-}

module UMIN.L00_Foundation.HomotopyTheory.LoopSpace where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.HITs.PropositionalTruncation as PT
open import UMIN.L00_Foundation.HomotopyTheory.Pointed

--------------------------------------------------
-- 1. ループ空間（Psypher スケルトン）
--------------------------------------------------

Ω : Pointed → Pointed
Ω X = record
  { Space = (Pointed.pt X ≡ Pointed.pt X)
  ; pt    = refl
  }

--------------------------------------------------
-- 2. Ω の関手性
--------------------------------------------------
--
-- 目標:
--   sym (pt-pres F) ∙ (λ i → f F (refl i)) ∙ pt-pres F ≡ refl
--
-- 注意: (λ i → f F (refl i)) は f F (pt A) の自明なループで、
--       定義上 refl と判定的に等しい。
--       したがって本質は sym p ∙ refl ∙ p ≡ refl の証明。
--
-- 戦略:
--   Step 1. lUnit の逆向き使用で refl ∙ p ≡ p を p に書き換える方向…
--           ではなく、sym lUnit を使うと逆向きに変形できる。
--   Step 2. ここでは「中央の refl を除去 → lCancel」の素直な経路を取る。
--           sym p ∙ refl ∙ p
--             ≡⟨ cong (sym p ∙_) (sym (lUnit p)) ⟩  -- refl ∙ p ≡ p の逆向き
--           sym p ∙ p
--             ≡⟨ lCancel p ⟩
--           refl
--
--   ※ lUnit : p ≡ refl ∙ p （Cubical.Foundations.GroupoidLaws の慣習）
--     sym (lUnit p) : refl ∙ p ≡ p
--
-- ※ Cubical stdlib の lUnit の向きはバージョンにより
--     lUnit : p ≡ refl ∙ p
--   または
--     lUnit : refl ∙ p ≡ p
--   の場合がある。Gemy 側で実コンパイル時に向きを確認し、
--   必要なら sym の有無を調整すること。
--------------------------------------------------

Ω-map : {A B : Pointed} → PointedMap A B → PointedMap (Ω A) (Ω B)
Ω-map {A} {B} F = record
  { f       = λ p →
      sym (PointedMap.pt-pres F)
      ∙ (λ i → PointedMap.f F (p i))
      ∙ PointedMap.pt-pres F
  ; pt-pres =
      -- sym p ∙ refl ∙ p ≡ refl の証明
      -- 中央の (λ i → f F (refl i)) は refl と判定等価
      cong (sym (PointedMap.pt-pres F) ∙_)
           (sym (lUnit (PointedMap.pt-pres F)))
      ∙ lCancel (PointedMap.pt-pres F)
  }

--------------------------------------------------
-- 3. Ω の二重適用
--------------------------------------------------

Ω² : Pointed → Pointed
Ω² X = Ω (Ω X)

--------------------------------------------------
-- 4. π₀ の定義（propositional truncation 経由）
--------------------------------------------------

π₀ : Pointed → Type₀
π₀ X = PT.∥ Pointed.Space X ∥₁
