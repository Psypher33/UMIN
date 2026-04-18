{-# OPTIONS --cubical --guardedness #-}
module UMIN.L03_Dynamic.Pentagon.PentagonAxiom_v2 where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import UMIN.L03_Dynamic.BG.BG_Step1_Step2

-- タスク1：sq₁-v3 の中身構成
sq₁-v3 : {G : Group} (a b c : Group.Carrier G) →
  loop {G} (Group._⋆_ G (Group._⋆_ G a b) c) ≡
  loop {G} (Group._⋆_ G a (Group._⋆_ G b c))
sq₁-v3 {G} a b c =
  let open Group G
  in cong (loop {G}) (sym (assoc a b c))

-- タスク2：Pentagon 五角形の型定義
postulate
  sq₁ sq₂ sq₃ sq₄ sq₅ : {G : Group} (a b c d : Group.Carrier G) → Type

PentagonDiagram : {G : Group} (a b c d : Group.Carrier G) → Type
PentagonDiagram {G} a b c d =
  (sq₁ {G} a b c d) ×
  ((sq₂ {G} a b c d) ×
  ((sq₃ {G} a b c d) ×
  ((sq₄ {G} a b c d) × (sq₅ {G} a b c d))))

-- タスク3：loop-unit-thm との接続（恒等辺のプロトタイプ）
unit-edge-sq : {G : Group} (a : Group.Carrier G) →
  loop {G} (Group._⋆_ G a (Group.unit G)) ≡ loop {G} a
unit-edge-sq {G} a =
  let open Group G
  in cong (loop {G}) (rid a)