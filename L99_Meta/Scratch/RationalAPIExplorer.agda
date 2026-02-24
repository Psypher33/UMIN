{-# OPTIONS --cubical --safe #-}

module UMIN.L99_Meta.Scratch.RationalAPIExplorer where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Rational.Base
open import Cubical.Data.Rational.Order

check-zero : ℚ
check-zero = 0 / 1

check-one : ℚ
check-one = 1 / 1

check-lt-type : {p q : ℚ} → p < q → Type
check-lt-type {p} {q} pf = p < q