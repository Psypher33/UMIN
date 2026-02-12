{-# OPTIONS --cubical --guardedness #-}

module UMIN.L01_Math.Algebraic_Structures.TheoremLayer.e8-roots where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int      using (ℤ; pos; negsuc; _·_; _+_)
open import Cubical.Data.Sum      using (_⊎_; inl; inr)
open import Cubical.Data.Sigma    using (Σ; _,_)

----------------------------------------------------------------
-- 基本パターン

pattern +₂ = pos 2
pattern ₀  = pos 0
pattern -₂ = negsuc 1

----------------------------------------------------------------
-- D₈座標（0, ±2）

Coord : ℤ → Type
Coord x =
  (x ≡ +₂) ⊎ ((x ≡ -₂) ⊎ (x ≡ ₀))

----------------------------------------------------------------
-- 4の倍数（構造版）

Div4 : ℤ → Type
Div4 n = Σ ℤ (λ k → n ≡ pos 4 · k)

----------------------------------------------------------------
-- 積の輸送ヘルパー

-- 修正版：k を明示的に指定せず、等式そのものを扱う
solve :
  ∀ {a b x y} {target : ℤ}
  → (p : a ≡ x)
  → (q : b ≡ y)
  → (x · y ≡ target)
  → (a · b ≡ target)
solve p q r =
  subst (λ t → t ≡ _)
        (sym (cong₂ _·_ p q))
        r

----------------------------------------------------------------
-- 座標積は常に4の倍数

coord-mul-4 : (a b : ℤ) → Coord a → Coord b → Div4 (a · b)

-- +2 * +2 = 4 = 4·1
coord-mul-4 a b (inl p) (inl q) =
  pos 1 ,
  solve p q refl

-- +2 * -2 = -4 = 4·(-1)
coord-mul-4 a b (inl p) (inr (inl q)) =
  negsuc 0 ,
  solve p q refl

-- +2 * 0 = 0
coord-mul-4 a b (inl p) (inr (inr q)) =
  ₀ ,
  solve p q refl

-- -2 * +2 = -4
coord-mul-4 a b (inr (inl p)) (inl q) =
  negsuc 0 ,
  solve p q refl

-- -2 * -2 = 4
coord-mul-4 a b (inr (inl p)) (inr (inl q)) =
  pos 1 ,
  solve p q refl

-- -2 * 0 = 0
coord-mul-4 a b (inr (inl p)) (inr (inr q)) =
  ₀ ,
  solve p q refl

-- 0 * anything = 0
coord-mul-4 a b (inr (inr p)) _ =
  ₀ ,
  subst (λ t → t ≡ pos 4 · ₀)
        (sym (cong (λ x → x · b) p))
        refl
