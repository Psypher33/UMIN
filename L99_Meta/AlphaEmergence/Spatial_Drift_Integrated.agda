{-# OPTIONS --cubical --safe --guardedness #-}

module UMIN.L99_Meta.AlphaEmergence.Spatial_Drift_Integrated where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Int as ℤ using (pos; ℤ)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Rationals.Base
open import Cubical.Data.Rationals.Properties
  using ( -_; _-_; _+_; _·_
        ; +InvL; +InvR; +IdL; +IdR; +Comm; +Assoc
        ; ·AnnihilL; ·AnnihilR; ·Comm; ·Assoc)
open import Cubical.Data.Rationals.Order as ℚO
open import Cubical.Relation.Nullary using (yes; no)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Int.Order as ℤO using (zero-≤pos; suc-≤-suc; <Dec)


_<ℚ_ : ℚ → ℚ → Type
_<ℚ_ = ℚO._<_

ℚ0 : ℚ
ℚ0 = 0

ℚ2 : ℚ
ℚ2 = 2

ℚ-k : ℚ
ℚ-k = [ pos 1 / 10 ]

ℚ-K : ℚ
ℚ-K = [ pos 5900 / 1 ]

-- ================================================================
-- 具体値の正値証明（<Dec を使用）
-- ================================================================

-- ℤで 0 < n を直接計算
0<ℤsuc : ∀ (n : ℕ) → ℤO._<_ (pos 0) (pos (suc n))
0<ℤsuc n = suc-≤-suc (zero-≤pos {n})

-- ℚの<の定義に直接代入
-- [0/1] < [2/1]: pos 0 · 1 ℤ.< pos 2 · 1 = 0 ℤ.< 2
0<2 : ℚ0 <ℚ ℚ2
0<2 with ℤO.<Dec (pos 0) (pos 2)
... | yes p = p
... | no ¬p = ⊥.elim (¬p (0<ℤsuc 1))

-- [0/1] < [1/10]: pos 0 · 10 ℤ.< pos 1 · 1 = 0 ℤ.< 1
0<k-MZV : ℚ0 <ℚ ℚ-k
0<k-MZV with ℤO.<Dec (pos 0) (pos 1)
... | yes p = p
... | no ¬p = ⊥.elim (¬p (0<ℤsuc 0))

-- [0/1] < [5900/1]: 0 ℤ.< 5900
0<K-Th229 : ℚ0 <ℚ ℚ-K
0<K-Th229 with ℤO.<Dec (pos 0) (pos 5900)
... | yes p = p
... | no ¬p = ⊥.elim (¬p (0<ℤsuc 5899))

-- ================================================================
-- 補助補題
-- ================================================================

neg-pos-is-neg : (a : ℚ) → ℚ0 <ℚ a → (- a) <ℚ ℚ0
neg-pos-is-neg a 0<a =
  transport
    (cong₂ _<ℚ_
      (+IdR (- a))
      (+InvL a))
    (ℚO.<-o+ ℚ0 a (- a) 0<a)

mul-pos-pos : (a b : ℚ) → ℚ0 <ℚ a → ℚ0 <ℚ b → ℚ0 <ℚ (a · b)
mul-pos-pos a b 0<a 0<b =
  transport
    (cong (_<ℚ (a · b)) (·AnnihilL b))
    (ℚO.<-·o ℚ0 a b 0<b 0<a)

mul-pos-neg-lt-zero : (a c : ℚ) → a <ℚ ℚ0 → ℚ0 <ℚ c → (c · a) <ℚ ℚ0
mul-pos-neg-lt-zero a c a<0 0<c =
  transport
    (cong₂ _<ℚ_ (·Comm a c) (·AnnihilL c))
    (ℚO.<-·o a ℚ0 c 0<c a<0)

-- ================================================================
-- 物理定数
-- ================================================================

A-const : ℚ → ℚ
A-const Γ = ℚ-K · (ℚ2 · (ℚ-k · Γ))

A-const-pos : (Γ : ℚ) → ℚ0 <ℚ Γ → ℚ0 <ℚ A-const Γ
A-const-pos Γ 0<Γ =
  mul-pos-pos ℚ-K (ℚ2 · (ℚ-k · Γ)) 0<K-Th229
    (mul-pos-pos ℚ2 (ℚ-k · Γ) 0<2
      (mul-pos-pos ℚ-k Γ 0<k-MZV 0<Γ))

-- ================================================================
-- 計算関数
-- ================================================================

compute-drift : ℚ → ℚ → ℚ
compute-drift Γ H = A-const Γ · (ℚ0 + (- (H · Γ)))

-- ================================================================
-- 空間ドリフト定理
-- ================================================================

Theorem-Spatial-Drift :
  (Γ Hv Hc : ℚ)
  → ℚ0 <ℚ Γ
  → Hc <ℚ Hv
  → ℚ0 <ℚ Hc
  → let dv = compute-drift Γ Hv
        dc = compute-drift Γ Hc
    in (dv <ℚ dc) × (dc <ℚ ℚ0)

Theorem-Spatial-Drift Γ Hv Hc pΓ pHcHv pHc0 =
  let
    A  = A-const Γ
    pA = A-const-pos Γ pΓ

    step1 : (Hc · Γ) <ℚ (Hv · Γ)
    step1 = ℚO.<-·o Hc Hv Γ pΓ pHcHv

    step2 : (- (Hv · Γ)) <ℚ (- (Hc · Γ))
    step2 = ℚO.<-+o-cancel (- (Hv · Γ)) (- (Hc · Γ)) (Hc · Γ)
              (transport
                (cong₂ _<ℚ_
                  (+Comm (Hc · Γ) (- (Hv · Γ)))
                  (sym (+InvL (Hc · Γ))))
                (transport
                  (cong ((Hc · Γ + (- (Hv · Γ))) <ℚ_)
                    (+InvR (Hv · Γ)))
                  (ℚO.<-+o (Hc · Γ) (Hv · Γ) (- (Hv · Γ)) step1)))

    step3 : (ℚ0 + (- (Hv · Γ))) <ℚ (ℚ0 + (- (Hc · Γ)))
    step3 = transport
              (cong₂ _<ℚ_
                (sym (+IdL (- (Hv · Γ))))
                (sym (+IdL (- (Hc · Γ)))))
              step2

    proof-v<c : (A · (ℚ0 + (- (Hv · Γ)))) <ℚ (A · (ℚ0 + (- (Hc · Γ))))
    proof-v<c = transport
                  (cong₂ _<ℚ_
                    (·Comm (ℚ0 + (- (Hv · Γ))) A)
                    (·Comm (ℚ0 + (- (Hc · Γ))) A))
                  (ℚO.<-·o (ℚ0 + (- (Hv · Γ))) (ℚ0 + (- (Hc · Γ))) A pA step3)

    HcΓ>0 : ℚ0 <ℚ (Hc · Γ)
    HcΓ>0 = mul-pos-pos Hc Γ pHc0 pΓ

    dΓc<0 : (ℚ0 + (- (Hc · Γ))) <ℚ ℚ0
    dΓc<0 = subst (_<ℚ ℚ0)
               (sym (+IdL (- (Hc · Γ))))
               (neg-pos-is-neg (Hc · Γ) HcΓ>0)

    proof-c<0 : (A · (ℚ0 + (- (Hc · Γ)))) <ℚ ℚ0
    proof-c<0 = mul-pos-neg-lt-zero (ℚ0 + (- (Hc · Γ))) A dΓc<0 pA

  in (proof-v<c , proof-c<0)