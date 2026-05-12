{-# OPTIONS --cubical --safe --guardedness #-}

module UMIN.L00_Foundation.HomotopyTheory.PuppeBoundary where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import UMIN.L00_Foundation.HomotopyTheory.Pointed
open import UMIN.L00_Foundation.HomotopyTheory.LoopSpace
open import UMIN.L00_Foundation.HomotopyTheory.HomotopyFiber

--------------------------------------------------
-- 1. 境界写像 ∂-base : Ω B → hofib(F)
--
-- ループ ℓ : pt B ≡ pt B を、ファイバー上の点
--   (pt A , pt-pres F ∙ sym ℓ)
-- に送る。これは Puppé sequence の核心構成。
--
-- pt-pres の証明：
--   目標 ∂-base F refl ≡ (pt A , pt-pres F)
--   ⟺   (pt A , pt-pres F ∙ sym refl) ≡ (pt A , pt-pres F)
--
--   第1成分: refl
--   第2成分: pt-pres F ∙ sym refl ≡ pt-pres F
--           sym refl は refl と判定等価なので
--           本質は pt-pres F ∙ refl ≡ pt-pres F
--           これは sym (rUnit (pt-pres F))。
--
--   ※ Cubical 慣習: rUnit : p ≡ p ∙ refl
--     したがって sym (rUnit p) : p ∙ refl ≡ p。
--     stdlib のバージョンにより向きが逆の場合は sym を外すこと。
--------------------------------------------------

∂-base : {A B : Pointed} (F : PointedMap A B)
       → PointedMap (Ω B) (hofibPt F)
∂-base {A} {B} F = record
  { f       = λ loop →
      (Pointed.pt A , PointedMap.pt-pres F ∙ sym loop)
  ; pt-pres =
      ΣPathP (refl , sym (rUnit (PointedMap.pt-pres F)))
  }

--------------------------------------------------
-- 2. ∂ の高次版：Ω² B → Ω(hofib F)
--
-- ※ Ω-map と ∂-base の合成として構成。
--   comp-pointed の引数順は (G ∘ F) なので注意。
--   Ω-map (∂-base F) : Ω(Ω B) → Ω(hofib F) として
--   そのまま使える。
--------------------------------------------------

∂-higher : {A B : Pointed} (F : PointedMap A B)
         → PointedMap (Ω (Ω B)) (Ω (hofibPt F))
∂-higher F = Ω-map (∂-base F)
