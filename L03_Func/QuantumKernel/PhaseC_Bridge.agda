{-# OPTIONS --cubical --safe --guardedness #-}

-- ================================================================
--  L03_Func/QuantumKernel/PhaseC_Bridge.agda
--  PhaseC_Master（証明完了済み）の核心を再輸出し
--  各骨格モジュールが参照できるようにする
-- ================================================================

module UMIN.L03_Func.QuantumKernel.PhaseC_Bridge where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
  using (rCancel; rUnit)
  renaming (assoc to pathAssoc)
open import Cubical.Foundations.Univalence

-- ================================================================
-- §1  Group 定義（PhaseC_Master と完全に同一）[✓]
-- ================================================================

record Group : Type₁ where
  field
    Carrier  : Type
    isSet-C  : isSet Carrier
    unit     : Carrier
    _⋆_      : Carrier → Carrier → Carrier
    inv      : Carrier → Carrier
    assoc    : (a b c : Carrier) → a ⋆ (b ⋆ c) ≡ (a ⋆ b) ⋆ c
    lid      : (g : Carrier) → unit ⋆ g ≡ g
    rid      : (g : Carrier) → g ⋆ unit ≡ g
    linv     : (g : Carrier) → inv g ⋆ g ≡ unit
    rinv     : (g : Carrier) → g ⋆ inv g ≡ unit
open Group

-- ================================================================
-- §2  分類空間 BG（PhaseC_Master と完全に同一）[✓]
-- ================================================================

data BG (G : Group) : Type where
  base      : BG G
  loop      : Carrier G → base ≡ base
  loop-comp : (a b : Carrier G)
            → loop (G ._⋆_ a b) ≡ loop a ∙ loop b

-- ================================================================
-- §3  佐々木随伴（right-mul-iso）[✓ PhaseC_Master から再掲]
-- ================================================================

right-mul-iso : {G : Group} → Carrier G → Iso (Carrier G) (Carrier G)
right-mul-iso {G} g = record
  { fun = λ x → G ._⋆_ x g
  ; inv = λ x → G ._⋆_ x (G .inv g)
  ; sec = λ e → sym (G .assoc e (G .inv g) g)
              ∙ cong (G ._⋆_ e) (G .linv g)
              ∙ G .rid e
  ; ret = λ e → sym (G .assoc e g (G .inv g))
              ∙ cong (G ._⋆_ e) (G .rinv g)
              ∙ G .rid e
  }

right-mul-equiv : {G : Group} → Carrier G → (Carrier G ≃ Carrier G)
right-mul-equiv {G} g = isoToEquiv (right-mul-iso {G} g)

-- ================================================================
-- §4  loop-unit-thm（ゼロ点の静寂）[✓ PhaseC_Master から再掲]
-- ================================================================

loop-unit-thm : {G : Group} → loop {G} (unit G) ≡ refl
loop-unit-thm {G} =
  let u  = unit G
      lu = loop {G} u
      p  : lu ≡ lu ∙ lu
      p  = sym (cong loop (G .lid u)) ∙ loop-comp u u
      pr : lu ∙ sym lu ≡ (lu ∙ lu) ∙ sym lu
      pr = cong (λ q → q ∙ sym lu) p
      lhs : lu ∙ sym lu ≡ refl
      lhs = rCancel lu
      rhs : (lu ∙ lu) ∙ sym lu ≡ lu
      rhs = sym (pathAssoc lu lu (sym lu))
          ∙ cong (λ q → lu ∙ q) (rCancel lu)
          ∙ sym (rUnit lu)
  in sym (sym lhs ∙ pr ∙ rhs)

-- ================================================================
-- §5  mul-equiv-comp（2体結合性）[✓]
-- ================================================================

mul-equiv-comp : {G : Group} (g h : Carrier G)
               → right-mul-equiv {G} (G ._⋆_ g h)
               ≡ compEquiv (right-mul-equiv {G} g) (right-mul-equiv {G} h)
mul-equiv-comp {G} g h =
  equivEq (funExt (λ x → G .assoc x g h))
