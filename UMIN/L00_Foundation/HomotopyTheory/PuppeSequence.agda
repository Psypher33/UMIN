{-# OPTIONS --cubical --safe --guardedness #-}

module UMIN.L00_Foundation.HomotopyTheory.PuppeSequence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Sigma
open import UMIN.L00_Foundation.HomotopyTheory.Pointed
open import UMIN.L00_Foundation.HomotopyTheory.LoopSpace
open import UMIN.L00_Foundation.HomotopyTheory.HomotopyFiber
open import UMIN.L00_Foundation.HomotopyTheory.PuppeBoundary

--------------------------------------------------
-- 1. LGT-1 の型（主定理 statement）
--
-- π₁(B) ↠ π₀(hofib(F)) の全射性。
-- ∥_∥₁ で包むことで「propositional な全射性」を表す。
--------------------------------------------------

LGT-1-type : {A B : Pointed} (F : PointedMap A B) → Type₀
LGT-1-type {A} {B} F =
  (c : Pointed.Space (hofibPt F))
  → ∥ Σ[ loop ∈ (Pointed.pt B ≡ Pointed.pt B) ]
        (PointedMap.f (∂-base F) loop ≡ c) ∥₁

--------------------------------------------------
-- 2. LGT-1 主定理（--safe 準拠版・実証明）
--
-- 旧 postulate を P1 案で除去。前提を path-connected
--    (a : Space A) → ∥ a ≡ pt A ∥₁
-- に強化し、Puppe 列の全射性を構成的に証明する。
--
-- loop の構成は当初スケッチから訂正：
--   sym (pt-pres F) ∙ cong (f F) (sym q) ∙ p
-- だと pt-pres F のキャンセルが起きず path-over が閉じない。
-- 順序を逆にした
--   sym p ∙ cong (f F) q ∙ pt-pres F
-- を採用することで pt-pres F ∙ sym loop が rCancel 経由で
-- cong (f F) (sym q) ∙ p に簡約され、compPath-filler' で
-- path-over が構成できる。
--------------------------------------------------

LGT-1 : {A B : Pointed} (F : PointedMap A B)
      → ((a : Pointed.Space A) → ∥ a ≡ Pointed.pt A ∥₁)
      → LGT-1-type F
LGT-1 {A} {B} F connA (a , p) =
  PT.rec PT.squash₁
    (λ (q : a ≡ Pointed.pt A) →
       let
         loop : Pointed.pt B ≡ Pointed.pt B
         loop = sym p
              ∙ cong (PointedMap.f F) q
              ∙ PointedMap.pt-pres F

         -- sym loop を symDistr で右側に展開：
         --   sym (sym p ∙ (cong (f F) q ∙ pt-pres F))
         --   ≡ sym (cong (f F) q ∙ pt-pres F) ∙ p
         --   ≡ (sym (pt-pres F) ∙ cong (f F) (sym q)) ∙ p
         --   ≡ sym (pt-pres F) ∙ cong (f F) (sym q) ∙ p
         -- ※ sym (sym p) ≡ p および sym (cong f q) ≡ cong f (sym q)
         --   は judgmental（cubical の interval primitive 由来）。
         sym-loop-expand :
             sym loop
           ≡ sym (PointedMap.pt-pres F)
             ∙ cong (PointedMap.f F) (sym q)
             ∙ p
         sym-loop-expand =
             sym loop
               ≡⟨ symDistr (sym p)
                    (cong (PointedMap.f F) q ∙ PointedMap.pt-pres F) ⟩
             sym (cong (PointedMap.f F) q ∙ PointedMap.pt-pres F) ∙ p
               ≡⟨ cong (_∙ p)
                    (symDistr (cong (PointedMap.f F) q)
                              (PointedMap.pt-pres F)) ⟩
             (sym (PointedMap.pt-pres F)
              ∙ cong (PointedMap.f F) (sym q)) ∙ p
               ≡⟨ sym (assoc _ _ _) ⟩
             sym (PointedMap.pt-pres F)
               ∙ cong (PointedMap.f F) (sym q) ∙ p
             ∎

         -- ∂-base F loop の第2成分の簡約：
         --   pt-pres F ∙ sym loop
         --   ≡ pt-pres F ∙ (sym (pt-pres F) ∙ cong (f F) (sym q) ∙ p)
         --   ≡ (pt-pres F ∙ sym (pt-pres F)) ∙ (cong (f F) (sym q) ∙ p)
         --   ≡ refl ∙ (cong (f F) (sym q) ∙ p)           (rCancel)
         --   ≡ cong (f F) (sym q) ∙ p                    (sym lUnit)
         lemma :
             PointedMap.pt-pres F ∙ sym loop
           ≡ cong (PointedMap.f F) (sym q) ∙ p
         lemma =
             PointedMap.pt-pres F ∙ sym loop
               ≡⟨ cong (PointedMap.pt-pres F ∙_) sym-loop-expand ⟩
             PointedMap.pt-pres F
               ∙ (sym (PointedMap.pt-pres F)
                  ∙ cong (PointedMap.f F) (sym q) ∙ p)
               ≡⟨ assoc _ _ _ ⟩
             (PointedMap.pt-pres F ∙ sym (PointedMap.pt-pres F))
               ∙ (cong (PointedMap.f F) (sym q) ∙ p)
               ≡⟨ cong (_∙ (cong (PointedMap.f F) (sym q) ∙ p))
                    (rCancel (PointedMap.pt-pres F)) ⟩
             refl ∙ (cong (PointedMap.f F) (sym q) ∙ p)
               ≡⟨ sym (lUnit _) ⟩
             cong (PointedMap.f F) (sym q) ∙ p
             ∎

         -- path-over の構成：
         --   compPath-filler' (cong (f F) (sym q)) p を symP で反転し、
         --   その左端を lemma で書き換える。
         filler :
             PathP (λ i → PointedMap.f F (sym q i) ≡ Pointed.pt B)
                   (cong (PointedMap.f F) (sym q) ∙ p)
                   p
         filler =
           symP (compPath-filler' (cong (PointedMap.f F) (sym q)) p)

         path-over :
             PathP (λ i → PointedMap.f F (sym q i) ≡ Pointed.pt B)
                   (PointedMap.pt-pres F ∙ sym loop)
                   p
         path-over =
           subst
             (λ x → PathP (λ i → PointedMap.f F (sym q i) ≡ Pointed.pt B)
                           x p)
             (sym lemma)
             filler

         eq : PointedMap.f (∂-base F) loop ≡ (a , p)
         eq = ΣPathP (sym q , path-over)
       in ∣ loop , eq ∣₁)
    (connA a)
