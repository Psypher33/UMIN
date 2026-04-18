{-# OPTIONS --safe --cubical --guardedness #-}
module UMIN.L03_Dynamic.CCT.UMIN_PhaseC_One_Group where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)

record Group : Type₁ where
  field
    Carrier : Type
    isSet-C : isSet Carrier  -- ★これが高次ノイズを完全に遮断する防波堤
    unit : Carrier
    _⋆_ : Carrier → Carrier → Carrier
    inv : Carrier → Carrier
    assoc : (a b c : Carrier) → a ⋆ (b ⋆ c) ≡ (a ⋆ b) ⋆ c
    lid : (g : Carrier) → unit ⋆ g ≡ g
    rid : (g : Carrier) → g ⋆ unit ≡ g
    linv : (g : Carrier) → inv g ⋆ g ≡ unit
    rinv : (g : Carrier) → g ⋆ inv g ≡ unit

data BG (G : Group) : Type where
  base : BG G
  loop : Group.Carrier G → base ≡ base
  loop-comp : (a b : Group.Carrier G) → loop (Group._⋆_ G a b) ≡ loop a ∙ loop b
  -- trunc は削除。Carrier の isSet 性により、トポロジーは自動的に安定相に入ります。

open Group

right-mul-iso : {G : Group} → Group.Carrier G → Iso (Group.Carrier G) (Group.Carrier G)
right-mul-iso {G} g = record {
  fun = λ x → Group._⋆_ G x g ;  
  inv = λ x → Group._⋆_ G x (Group.inv G g) ;  
  sec = λ elem → sym (Group.assoc G elem (Group.inv G g) g) ∙ cong (Group._⋆_ G elem) (Group.linv G g) ∙ Group.rid G elem ;
  ret = λ elem → sym (Group.assoc G elem g (Group.inv G g)) ∙ cong (Group._⋆_ G elem) (Group.rinv G g) ∙ Group.rid G elem }

right-mul-equiv : {G : Group} → Group.Carrier G → (Group.Carrier G ≃ Group.Carrier G)
right-mul-equiv {G} g = isoToEquiv (right-mul-iso {G} g)