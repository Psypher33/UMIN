{-# OPTIONS --safe --cubical --guardedness #-}

module UMIN.L03_Func.QuantumKernel.UMIN_PhaseC_three_Cover where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import UMIN.L03_Func.QuantumKernel.UMIN_PhaseC_One_Group
open import UMIN.L03_Func.QuantumKernel.UMIN_PhaseC_two_Algebra

-- ============================================================
-- 🌟 5. Universal Cover (トポロジーと代数の究極の同期)
-- hSet への無理な射影をやめ、直接 Type へ同期させます。
-- ============================================================
UniversalCover : {G : Group} → BG G → Type
UniversalCover {G} base = Group.Carrier G
UniversalCover {G} (loop g i) = ua (right-mul-equiv {G} g) i
UniversalCover {G} (loop-comp g h i j) = ua-mul-comp {G} g h i j

-- ============================================================
-- 🌟 6. Encode & Decode (ホモロジー的還流の真の姿)
-- ============================================================
decode : {G : Group} → Group.Carrier G → base {G} ≡ base {G}
decode g = loop g

encode : {G : Group} → base {G} ≡ base {G} → Group.Carrier G
encode {G} p = transport (λ i → UniversalCover {G} (p i)) (Group.unit G)

-- ============================================================
-- 🌟 7. β規則 (量子カーネルの演算健全性の絶対証明)
-- ============================================================
encode-decode : {G : Group} (g : Group.Carrier G) → encode {G} (decode g) ≡ g
encode-decode {G} g = 
  transport (λ i → ua (right-mul-equiv {G} g) i) (Group.unit G)
    ≡⟨ uaβ (right-mul-equiv {G} g) (Group.unit G) ⟩
  Group._⋆_ G (Group.unit G) g
    ≡⟨ Group.lid G g ⟩
  g ∎