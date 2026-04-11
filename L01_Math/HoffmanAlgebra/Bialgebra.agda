{-# OPTIONS --cubical --safe --guardedness #-}

open import Cubical.Algebra.Ring.Base

module UMIN.L01_Math.HoffmanAlgebra.Bialgebra {ℓ} (R : Ring ℓ) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List
open import Cubical.Data.Prod hiding (map)

private
  Carrier : Type ℓ
  Carrier = fst R

open RingStr (snd R) renaming
  ( 0r to 0#
  ; _·_ to _*_
  )

-- =====================================================
-- §1. Hoffman代数の基礎
-- =====================================================
data Letter : Type₀ where
  X₀ X₁ : Letter

Word : Type₀
Word = List Letter

FPS-NonComm : Type ℓ
FPS-NonComm = Word → Carrier

-- =====================================================
-- §2. シャッフル積 (Shuffle Product / Intertwining)
-- あなたの実装を完全採用。被覆空間の「経路の交わり」を記述する。
-- =====================================================
_sha_ : Word → Word → List Word
[] sha v = v ∷ []
u sha [] = u ∷ []
(x ∷ u) sha (y ∷ v) = 
  map (λ w → x ∷ w) (u sha (y ∷ v)) ++ 
  map (λ w → y ∷ w) ((x ∷ u) sha v)

-- =====================================================
-- §3. 余積 (Coproduction / Branching)
-- 経路の「分岐」を記述する。シャッフル積の双対操作。
-- =====================================================
de-concat : Word → List (Word × Word)
de-concat [] = ([] , []) ∷ []
de-concat (x ∷ xs) = 
  ([] , x ∷ xs) ∷ map (λ p → (x ∷ proj₁ p) , proj₂ p) (de-concat xs)

-- =====================================================
-- §4. 評価写像 (Evaluation)
-- Wordの多重集合(List)に対するFPSの線形拡張
-- =====================================================
eval-sum : FPS-NonComm → List Word → Carrier
eval-sum f [] = 0#
eval-sum f (w ∷ ws) = f w + eval-sum f ws

-- =====================================================
-- §5. 💥 Group-like 条件 (The Heart of the Associator)
-- =====================================================
-- 任意の FPS f がシャッフル関係式を満たすことの厳密な型定義。
-- UMIN理論において、これが「分岐したコサイクルが矛盾なく合流する」
-- ための究極のコヒーレンス条件（ゲージ不変性）となります。

Is-GroupLike : FPS-NonComm → Type ℓ
Is-GroupLike f = ∀ (u v : Word) → eval-sum f (u sha v) ≡ f u * f v

-- =====================================================
-- 🗡️ [山口からの挑戦状：線形性の証明]
-- =====================================================
-- シャッフル積の展開において、eval-sum がリストの結合 (++) に対して
-- 加法的（準同型）に振る舞うことを証明してください。
-- この補題が、シャッフル関係式を帰納法で解き明かすための「要」となります。

eval-sum-++ : ∀ (f : FPS-NonComm) (L1 L2 : List Word) → 
  eval-sum f (L1 ++ L2) ≡ eval-sum f L1 + eval-sum f L2
eval-sum-++ f [] L2 =
  sym (+IdL (eval-sum f L2))
eval-sum-++ f (w ∷ ws) L2 =
  cong (λ z → f w + z) (eval-sum-++ f ws L2)
    ∙ +Assoc (f w) (eval-sum f ws) (eval-sum f L2)