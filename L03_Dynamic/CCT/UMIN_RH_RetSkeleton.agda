{-# OPTIONS --cubical  --guardedness #-}

module UMIN.L03_Dynamic.CCT.UMIN_RH_RetSkeleton (X : Set₀) (V : Set₀) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma

-- 既存モジュール（Lemma は本ファイルで未使用のため読み込まない）
open import UMIN.L01_Arithmetic.Motives.UMIN_RH_Base X V
open import UMIN.L03_Dynamic.CCT.UMIN_RH_Fiber X V

------------------------------------------------------------------------
-- 1. 基本的な道具の定義 (to, from, to-from-base)
------------------------------------------------------------------------

postulate
  to   : ∀ {L : LocalSystem} {x : X}
       → TotalFiber (Cov L) (Loc→Cocycle L) x
       → F L x

  from : ∀ {L : LocalSystem} {x : X}
       → F L x
       → TotalFiber (Cov L) (Loc→Cocycle L) x

  to-from-base : ∀ {L : LocalSystem} {x : X}
               → (i : Index (Cov L)) (ui : U (Cov L) i x) (v : V)
               → from {L} {x} (to {L} {x} (base {c = Loc→Cocycle L} i ui v))
               ≡ base {c = Loc→Cocycle L} i ui v

------------------------------------------------------------------------
-- 2. 補助的な証明の定義 (ret-isSet)
------------------------------------------------------------------------

postulate
  -- to, from の定義の後に書くことでスコープエラーを防ぎます
  ret-isSet : ∀ {L : LocalSystem} {x : X}
            → (t : TotalFiber (Cov L) (Loc→Cocycle L) x)
            → isSet (from {L} {x} (to {L} {x} t) ≡ t)

------------------------------------------------------------------------
-- 3. base-case
------------------------------------------------------------------------

base-case : {L : LocalSystem} {x : X}
  → (i : Index (Cov L))
  → (ui : U (Cov L) i x)
  → (v : V)
  → from {L} {x} (to {L} {x} (base {c = Loc→Cocycle L} i ui v))
  ≡ base {c = Loc→Cocycle L} i ui v
base-case i ui v = to-from-base i ui v

------------------------------------------------------------------------
-- 4. paste-case
------------------------------------------------------------------------

paste-case : {L : LocalSystem} {x : X}
  → (i j : Index (Cov L))
  → (ui : U (Cov L) i x)
  → (uj : U (Cov L) j x)
  → (v : V)
  → PathP (λ k → from {L} {x} (to {L} {x} (paste {c = Loc→Cocycle L} i j ui uj v k))
                ≡ paste {c = Loc→Cocycle L} i j ui uj v k)
          (base-case i ui v)
          (base-case j uj (equivFun (g (Loc→Cocycle L) i j x (ui , uj)) v))
paste-case {L} {x} i j ui uj v =
  isProp→PathP
    (λ k → TotalFiber-isSet {c = Loc→Cocycle L}
             (from {L} {x} (to {L} {x} (p k))) (p k))
    (base-case i ui v)
    (base-case j uj (equivFun (g (Loc→Cocycle L) i j x (ui , uj)) v))
  where
    p : I → TotalFiber (Cov L) (Loc→Cocycle L) x
    p k = paste {c = Loc→Cocycle L} i j ui uj v k

------------------------------------------------------------------------
-- 5. ret (完成)
------------------------------------------------------------------------

ret : {L : LocalSystem} {x : X}
  → (t : TotalFiber (Cov L) (Loc→Cocycle L) x)
  → from {L} {x} (to {L} {x} t) ≡ t

ret {L} {x} t =
  TotalFiber-elim {c = Loc→Cocycle L}
    {P = λ t₁ → from {L} {x} (to {L} {x} t₁) ≡ t₁}
    (λ t₁ → ret-isSet t₁)
    base-case
    paste-case
    t
