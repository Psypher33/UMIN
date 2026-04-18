{-# OPTIONS --cubical --safe --guardedness #-}

open import Cubical.Foundations.Prelude
open import UMIN.L00_Foundation.Logic.WeakMonoidalCategory

module UMIN.L00_Foundation.Instance.AdPhi
  {ℓobj ℓhom}
  (C : WeakMonoidalCategory {ℓobj} {ℓhom})
  (ΦObj ΦInvObj : WeakMonoidalCategory.Obj C)
  where

open WeakMonoidalCategory C

-- ============================================================
-- ⚡ 1. 顕在化の共役作用 Ad_Φ の定義
-- ============================================================

Ad₀ : Obj → Obj
Ad₀ X = ΦObj ⊗ (X ⊗ ΦInvObj)

Ad₁ : ∀ {A B} → Hom A B → Hom (Ad₀ A) (Ad₀ B)
Ad₁ f = tensorHom id (tensorHom f id)

-- ============================================================
-- 🛡️ 2. 因果律の保存証明（All Done 確定ルート！）
-- ============================================================

-- 💡 証明1：停止(id)している宇宙は、顕在化しても停止(id)したままである
Ad-id-proof : ∀ {A : Obj} → Ad₁ (id {A}) ≡ id {A = Ad₀ A}
Ad-id-proof {A} =
  tensorHom id (tensorHom id id)
    ≡⟨ cong (λ x → tensorHom id x) (tensor-id {A} {ΦInvObj}) ⟩
  tensorHom id id
    ≡⟨ tensor-id {ΦObj} {A ⊗ ΦInvObj} ⟩
  id ∎

-- 💡 補題：停止(id)の合成は停止(id)である
id-circ-id : ∀ {X : Obj} → id {X} ∘ id {X} ≡ id {X}
id-circ-id {X} = id-left (id {X})

-- 💡 証明2：因果(fとg)の連続は、顕在化させても順番通りに連続する！
Ad-comp-proof : ∀ {A B D : Obj} (f : Hom B D) (g : Hom A B) → Ad₁ (f ∘ g) ≡ Ad₁ f ∘ Ad₁ g
Ad-comp-proof {A} {B} {D} f g =
  tensorHom id (tensorHom (f ∘ g) id)
    ≡⟨ sym (cong (λ x → tensorHom id (tensorHom (f ∘ g) x)) (id-circ-id {ΦInvObj})) ⟩
  tensorHom id (tensorHom (f ∘ g) (id ∘ id))
    ≡⟨ cong (tensorHom id) (tensor-comp g f id id) ⟩
  tensorHom id ((tensorHom f id) ∘ (tensorHom g id))
    ≡⟨ sym (cong (λ x → tensorHom x ((tensorHom f id) ∘ (tensorHom g id))) (id-circ-id {ΦObj})) ⟩
  tensorHom (id ∘ id) ((tensorHom f id) ∘ (tensorHom g id))
    ≡⟨ tensor-comp id id (tensorHom g id) (tensorHom f id) ⟩
  (tensorHom id (tensorHom f id)) ∘ (tensorHom id (tensorHom g id)) ∎