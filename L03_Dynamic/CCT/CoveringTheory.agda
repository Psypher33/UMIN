{-# OPTIONS --cubical --safe --guardedness #-}

module UMIN.L03_Dynamic.CCT.CoveringTheory where

open import Agda.Primitive
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma using (Σ; _×_; _,_; fst; snd)
open import Cubical.Data.Unit using (Unit; tt)

-- =========================================================
-- 基本：ループ空間 Ω
-- =========================================================

Ω : ∀ {ℓ} (X : Type ℓ) (x : X) → Type ℓ
Ω X x = Path X x x

-- =========================================================
-- 自己同型（軽量版）
-- =========================================================

record Aut {ℓ} (A : Type ℓ) : Type ℓ where
  constructor mkAut
  field
    to   : A → A
    inv  : A → A

open Aut

-- =========================================================
-- Covering 的構造（最小骨格）
-- =========================================================

record ObservableCovering {ℓ} (X : Type ℓ) : Type (lsuc ℓ) where
  field
    Fiber     : X → Type ℓ

    -- 経路に沿った輸送
    fiberTransport :
      {x y : X} →
      Path X x y →
      Fiber x → Fiber y

    fiberTransport-refl :
      {x : X} →
      fiberTransport {x = x} {y = x} refl ≡ (λ v → v)

    fiberTransport-comp :
      {x y z : X} →
      (p : Path X x y) →
      (q : Path X y z) →
      fiberTransport (p ∙ q)
      ≡
      (fiberTransport q) ∘ (fiberTransport p)

open ObservableCovering

-- =========================================================
-- ループ作用（モノドロミー）
-- =========================================================

loop-action :
  ∀ {ℓ} {X : Type ℓ}
  (C : ObservableCovering X)
  (x : X) →
  Ω X x →
  Fiber C x → Fiber C x
loop-action C x p = fiberTransport C p

-- =========================================================
-- q-生成子（Rの抽象起源）
-- =========================================================

q-gen :
  ∀ {ℓ} {X : Type ℓ}
  (C : ObservableCovering X)
  (x : X) →
  Ω X x →
  Aut (Fiber C x)
q-gen C x p = mkAut
  (loop-action C x p)
  (loop-action C x (sym p))

-- =========================================================
-- Functoriality（Markov-I の影）
-- =========================================================

loop-id :
  ∀ {ℓ} {X : Type ℓ}
  (C : ObservableCovering X)
  (x : X) →
  loop-action C x refl ≡ (λ v → v)
loop-id C x = fiberTransport-refl C {x = x}

loop-comp :
  ∀ {ℓ} {X : Type ℓ}
  (C : ObservableCovering X)
  (x : X)
  (p q : Ω X x) →
  loop-action C x (p ∙ q)
  ≡
  (loop-action C x q) ∘ (loop-action C x p)
loop-comp C x p q = fiberTransport-comp C p q

-- =========================================================
-- Trace 的構造（ホモトピー固定点の影）
-- =========================================================

isFixed :
  ∀ {ℓ} {A : Type ℓ} →
  (f : A → A) → A → Type ℓ
isFixed f a = f a ≡ a

Trace :
  ∀ {ℓ} {A : Type ℓ} →
  (f : A → A) → Type ℓ
Trace {A = A} f = Σ A (isFixed f)

-- =========================================================
-- Partial Trace の最小骨格
-- （まだ contract/cup-cap は入れない）
-- =========================================================

PartialTrace :
  ∀ {ℓ} {A : Type ℓ} →
  ((A × A) → (A × A)) →
  (A → A)
PartialTrace f a = fst (f (a , snd (f (a , a))))  -- ダミー（後で差し替え）

-- =========================================================
-- z（ホロノミー）のプレースホルダ
-- =========================================================

Scalar : Type
Scalar = Unit

z : Scalar
z = tt

-- 「ループが非自明ならスカラーが出る」雛形
Holonomy :
  ∀ {ℓ} {X : Type ℓ}
  (C : ObservableCovering X)
  (x : X)
  (p : Ω X x) →
  Scalar
Holonomy C x p = z
