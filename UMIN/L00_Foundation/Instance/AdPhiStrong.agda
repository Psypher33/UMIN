{-# OPTIONS --cubical --guardedness #-}

module UMIN.L00_Foundation.Instance.AdPhiStrong where

open import Cubical.Foundations.Prelude hiding (I)
open import UMIN.L00_Foundation.Logic.WeakMonoidalCategory
open import UMIN.L00_Foundation.Logic.MonoidalFunctor
import UMIN.L00_Foundation.Instance.AdPhi as AdPhiBase

module _
  {ℓobj ℓhom}
  (C : WeakMonoidalCategory {ℓobj} {ℓhom})
  (ΦObj ΦInvObj : WeakMonoidalCategory.Obj C)
  where

  open WeakMonoidalCategory C
  open AdPhiBase C ΦObj ΦInvObj public

  -- ============================================================
  -- 🌌 空間のねじれ（μ）と真空の構造（ε）の公理化
  -- ============================================================

  postulate
    -- アソシエータによる空間の「編み込み」経路
    Ad-μ-to   : ∀ A B → Hom (Ad₀ (A ⊗ B)) (Ad₀ A ⊗ Ad₀ B)
    Ad-μ-from : ∀ A B → Hom (Ad₀ A ⊗ Ad₀ B) (Ad₀ (A ⊗ B))
    Ad-μ-inv-right : ∀ A B → Ad-μ-to A B ∘ Ad-μ-from A B ≡ id
    Ad-μ-inv-left  : ∀ A B → Ad-μ-from A B ∘ Ad-μ-to A B ≡ id

    -- 顕在化した真空と元の真空を結ぶ経路
    Ad-ε-to   : Hom (Ad₀ I) I
    Ad-ε-from : Hom I (Ad₀ I)
    Ad-ε-inv-right : Ad-ε-to ∘ Ad-ε-from ≡ id
    Ad-ε-inv-left  : Ad-ε-from ∘ Ad-ε-to ≡ id

  -- ============================================================
  -- Strong monoidal endofunctor instance
  -- ============================================================

  AdΦ : StrongMonoidalEndofunctor C
  AdΦ .StrongMonoidalEndofunctor.F₀ = Ad₀
  AdΦ .StrongMonoidalEndofunctor.F₁ = Ad₁
  AdΦ .StrongMonoidalEndofunctor.F-id = Ad-id-proof
  AdΦ .StrongMonoidalEndofunctor.F-comp = Ad-comp-proof
  
  -- 💡 postulateで定義した部品をパズルのようにはめ込む！
  AdΦ .StrongMonoidalEndofunctor.μ = λ A B → record 
    { to = Ad-μ-to A B 
    ; from = Ad-μ-from A B 
    ; inv-right = Ad-μ-inv-right A B 
    ; inv-left = Ad-μ-inv-left A B 
    }
  AdΦ .StrongMonoidalEndofunctor.ε_unit = record 
    { to = Ad-ε-to 
    ; from = Ad-ε-from 
    ; inv-right = Ad-ε-inv-right 
    ; inv-left = Ad-ε-inv-left 
    }