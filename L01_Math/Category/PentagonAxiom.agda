{-# OPTIONS --safe --cubical --guardedness #-}
module UMIN.L01_Math.Category.PentagonAxiom where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Ring

-- Ring引数（Pentagon_Coherenceと合わせる）
module PentagonAxiom {ℓ} (R : Ring ℓ) where

  -- Pentagon_Coherence は FPS_Base R を public で再エクスポート（二重 import 禁止）
  open import UMIN.L00_Core.Logic.Pentagon_Coherence R

  -- ★A案：Obj = FormalPowerSeries と定義（特化による完全証明ルート）
  Obj : Type ℓ
  Obj = FormalPowerSeries

  -- α-path は WithAssoc の引数にしかないので、五角形の型は結合子 α でパラメトリックにする
  AssocPath : Type ℓ
  AssocPath = (A B C : Obj) → (A ⊗ B) ⊗ C ≡ A ⊗ (B ⊗ C)

  Pentagon : AssocPath → (w x y z : Obj) → Type ℓ
  Pentagon α w x y z =
    ( cong (_⊗ z) (α w x y)
    ∙ α w (x ⊗ y) z
    ∙ cong (w ⊗_) (α x y z) )
    ≡
    ( α (w ⊗ x) y z
    ∙ α w x (y ⊗ z) )

  -- WithAssoc.WithPentagonCoh.pentagon-final は α と五角形コヒーレンスを与えた上で点wiseに適用
  pentagon-holds :
      (α : AssocPath)
      (coh : ∀ A B C D → Pentagon α A B C D)
      (w x y z : Obj)
    → Pentagon α w x y z
  pentagon-holds α coh w x y z =
    WithAssoc.WithPentagonCoh.pentagon-final α coh w x y z