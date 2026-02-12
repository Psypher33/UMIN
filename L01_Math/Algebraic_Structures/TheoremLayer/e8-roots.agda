{-# OPTIONS --cubical --guardedness #-}

module UMIN.L01_Math.Algebraic_Structures.TheoremLayer.e8-roots where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int   using (ℤ; pos; negsuc; _·_; _+_)
open import Cubical.Data.Sum   using (_⊎_; inl; inr)

pattern +₂ = pos 2
pattern ₀  = pos 0
pattern -₂ = negsuc 1

Coord : ℤ → Type
Coord x =
  (x ≡ +₂) ⊎ ((x ≡ -₂) ⊎ (x ≡ ₀))

Prod4 : ℤ → Type
Prod4 n =
  (n ≡ pos 0)    ⊎
  ((n ≡ pos 4)    ⊎
  ((n ≡ pos 8)    ⊎
  ((n ≡ negsuc 3) ⊎   -- -4
  (n ≡ negsuc 7))))   -- -8

-- 型変換ヘルパー関数
solve : ∀ {a b x y : ℤ}
      → (p : a ≡ x)
      → (q : b ≡ y)
      → Prod4 (x · y)
      → Prod4 (a · b)
solve p q val = subst Prod4 (sym (cong₂ _·_ p q)) val

-- 実装
-- ポイント: 全7行で 3x3=9 通りのパターンを網羅しています。
-- 最後の「_ (inr (inr q))」という行は不要だったので削除しました。
coord-mul-4 : (a b : ℤ) → Coord a → Coord b → Prod4 (a · b)
coord-mul-4 a b (inl p)          (inl q)          = solve p q (inr (inl refl))                -- +2 * +2 = +4
coord-mul-4 a b (inl p)          (inr (inl q))    = solve p q (inr (inr (inr (inl refl))))    -- +2 * -2 = -4
coord-mul-4 a b (inl p)          (inr (inr q))    = solve p q (inl refl)                      -- +2 * 0  = 0
coord-mul-4 a b (inr (inl p))    (inl q)          = solve p q (inr (inr (inr (inl refl))))    -- -2 * +2 = -4
coord-mul-4 a b (inr (inl p))    (inr (inl q))    = solve p q (inr (inl refl))                -- -2 * -2 = +4
coord-mul-4 a b (inr (inl p))    (inr (inr q))    = solve p q (inl refl)                      -- -2 * 0  = 0
coord-mul-4 a b (inr (inr p))    _                = inl (cong (λ x → x · b) p)                -- 0  * _  = 0