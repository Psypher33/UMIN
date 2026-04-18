{-# OPTIONS --cubical --guardedness #-}
module test_lt where
open import Cubical.Foundations.Prelude
open import Cubical.Data.Rationals.Base
open import Cubical.Data.Rationals.Properties using (-_; _+_; +IdR; +InvL)
open import Cubical.Data.Rationals.Order as ℚO

_<ℚ_ : ℚ → ℚ → Type
_<ℚ_ = ℚO._<_

ℚ0 : ℚ
ℚ0 = 0

neg-pos-is-neg : (a : ℚ) → ℚ0 <ℚ a → (- a) <ℚ ℚ0
neg-pos-is-neg a 0<a =
  transport
    (cong₂ _<ℚ_ (+IdR (- a)) (+InvL a))
    (ℚO.<-o+ ℚ0 a (- a) 0<a)
