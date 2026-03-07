{-# OPTIONS --safe --cubical --guardedness #-}
module UMIN.L03_Func.QuantumKernel.UMIN_PhaseC_two_Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws using (rUnit; rCancel) renaming (assoc to pathAssoc)
open import UMIN.L03_Func.QuantumKernel.UMIN_PhaseC_One_Group -- ファイル1をインポート

loop-unit-thm : {G : Group} → loop {G} (Group.unit G) ≡ refl
loop-unit-thm {G} = let
  u = Group.unit G ; lu = loop {G} u
  p : lu ≡ lu ∙ lu
  p = sym (cong loop (Group.lid G u)) ∙ loop-comp u u
  p-right : lu ∙ sym lu ≡ (lu ∙ lu) ∙ sym lu
  p-right = cong (λ q → q ∙ sym lu) p
  lhs : lu ∙ sym lu ≡ refl
  lhs = rCancel lu
  rhs : (lu ∙ lu) ∙ sym lu ≡ lu
  rhs = sym (pathAssoc lu lu (sym lu)) ∙ cong (λ q → lu ∙ q) (rCancel lu) ∙ sym (rUnit lu)
  in sym (sym lhs ∙ p-right ∙ rhs)

module WithGroup (G : Group) where
  Car = Group.Carrier G
  assocG : (a b c : Car) → (Group._⋆_ G a (Group._⋆_ G b c)) ≡ (Group._⋆_ G (Group._⋆_ G a b) c)
  assocG = Group.assoc G
  mul-comp-fun-aux : (a b : Car) → fst (right-mul-equiv {G} (Group._⋆_ G a b)) ≡ fst (compEquiv (right-mul-equiv {G} a) (right-mul-equiv {G} b))
  mul-comp-fun-aux a b = funExt (λ (x : Car) → assocG x a b)

mul-comp-fun : {G : Group} (a b : Group.Carrier G)
  → fst (right-mul-equiv {G} (Group._⋆_ G a b)) ≡ fst (compEquiv (right-mul-equiv {G} a) (right-mul-equiv {G} b))
mul-comp-fun {G} a b = WithGroup.mul-comp-fun-aux G a b

mul-equiv-comp : {G : Group} (g h : Group.Carrier G)
  → right-mul-equiv {G} (Group._⋆_ G g h) ≡ compEquiv (right-mul-equiv {G} g) (right-mul-equiv {G} h)
mul-equiv-comp {G} g h = equivEq (mul-comp-fun {G} g h)

ua-mul-comp : {G : Group} (g h : Group.Carrier G)
  → ua (right-mul-equiv {G} (Group._⋆_ G g h)) ≡ ua (right-mul-equiv {G} g) ∙ ua (right-mul-equiv {G} h)
ua-mul-comp {G} g h = cong ua (mul-equiv-comp {G} g h) ∙ uaCompEquiv (right-mul-equiv {G} g) (right-mul-equiv {G} h)