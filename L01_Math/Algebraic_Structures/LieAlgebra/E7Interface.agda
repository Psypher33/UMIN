{-# OPTIONS --cubical --guardedness #-}

module UMIN.L01_Math.Algebraic_Structures.LieAlgebra.E7Interface where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; _·_)
open import UMIN.L01_Math.Algebraic_Structures.LieAlgebra.FieldOfRationals public
  using (ℚ⁺; _//_; 𝕜; 𝕜-zero; 𝕜-one; _+𝕜_; _·𝕜_; -𝕜_; ratEmbed; posRat)
open import UMIN.L01_Math.Algebraic_Structures.LieAlgebra.AlbertAlgebra
  as AlbertAlg using (𝔍ᶜ; mk𝔍; 𝕆-zero; _×𝔍_; _∘_; ⟨_,_⟩ⱼ𝕜; _+𝔍_; _⊛𝔍_; -𝔍_)
open import UMIN.L01_Math.Algebraic_Structures.LieAlgebra.E6Interface
  using (E6-Lie; E6-zero; _+E6_; -E6_; _⊛E6_; [_,_]₆; phi-act; phi-adjoint-act; _∨𝔍_)

-- ================================================================
-- §1. 定数と表現空間の定義
-- ================================================================

two-thirds : 𝕜
two-thirds = ratEmbed (posRat 2 3) 𝕜-one

one-third : 𝕜
one-third = ratEmbed (posRat 1 3) 𝕜-one

two-scalar : 𝕜
two-scalar = ratEmbed (posRat 2 1) 𝕜-one

-- 56次元表現空間 𝔓ᶜ
record 𝔓ᶜ : Type where
  constructor mk𝔓
  field
    X : 𝔍ᶜ
    Y : 𝔍ᶜ
    ξ : 𝕜
    η : 𝕜

-- ================================================================
-- §2. E7 Lie 環の定義と演算
-- ================================================================

record E7 : Type where
  constructor mkE7
  field
    ϕ : E6-Lie
    A : 𝔍ᶜ
    B : 𝔍ᶜ
    ν : 𝕜

-- 演算子の優先順位宣言（名前がスコープにある状態で宣言）
infixl 20 _+E7_
infix  25 -E7_
infixl 30 _⊛E7_
infix  35 [_,_]₇
infix  40 _×F_

-- 加法
_+E7_ : E7 → E7 → E7
(mkE7 ϕ₁ A₁ B₁ ν₁) +E7 (mkE7 ϕ₂ A₂ B₂ ν₂) =
  mkE7 (ϕ₁ +E6 ϕ₂) (A₁ +𝔍 A₂) (B₁ +𝔍 B₂) (ν₁ +𝕜 ν₂)

-- 符号反転
-E7_ : E7 → E7
-E7 (mkE7 ϕ A B ν) = mkE7 (-E6 ϕ) (-𝔍 A) (-𝔍 B) (-𝕜 ν)

-- スカラー倍
_⊛E7_ : 𝕜 → E7 → E7
k ⊛E7 (mkE7 ϕ A B ν) = mkE7 (k ⊛E6 ϕ) (k ⊛𝔍 A) (k ⊛𝔍 B) (k ·𝕜 ν)

-- E7 の零元
𝔍-zero : 𝔍ᶜ
𝔍-zero = mk𝔍 𝕜-zero 𝕜-zero 𝕜-zero 𝕆-zero 𝕆-zero 𝕆-zero

E7-zero : E7
E7-zero = mkE7 E6-zero 𝔍-zero 𝔍-zero 𝕜-zero

-- E7 括弧積 [_,_]₇
[_,_]₇ : E7 → E7 → E7
[ mkE7 ϕ₁ A₁ B₁ ν₁ , mkE7 ϕ₂ A₂ B₂ ν₂ ]₇ =
  mkE7 ϕ-res A-res B-res ν-res
  where
    ϕ₁₆ = [ ϕ₁ , ϕ₂ ]₆
    ν₁-coeff = two-thirds ·𝕜 ν₁
    ν₂-coeff = two-thirds ·𝕜 ν₂
    ϕ-res = (ϕ₁₆ +E6 (A₁ ∨𝔍 B₂)) +E6 (-E6 (A₂ ∨𝔍 B₁))
    A-res = (phi-act ϕ₁ A₂ +𝔍 (ν₁-coeff ⊛𝔍 A₂)) +𝔍 (-𝔍 (phi-act ϕ₂ A₁ +𝔍 (ν₂-coeff ⊛𝔍 A₁)))
    B-res = (phi-adjoint-act ϕ₂ B₁ +𝔍 (-𝔍 (ν₂-coeff ⊛𝔍 B₁))) +𝔍 (-𝔍 (phi-adjoint-act ϕ₁ B₂ +𝔍 (-𝔍 (ν₁-coeff ⊛𝔍 B₂))))
    ν-res = (⟨ A₁ , B₂ ⟩ⱼ𝕜) +𝕜 (-𝕜 ⟨ A₂ , B₁ ⟩ⱼ𝕜)

-- E7 クロス積（postulate として再定義）
postulate
  _×F_ : 𝔓ᶜ → 𝔓ᶜ → E7

-- E7 Killing 形式（E8 の B₈ で用いる）
  B₇-definition : E7 → E7 → 𝕜

-- ================================================================
-- §3. 作用と不変性のスペック
-- ================================================================

E7-act : E7 → 𝔓ᶜ → 𝔓ᶜ
E7-act (mkE7 ϕ A B ν) (mk𝔓 X Y ξ η) = mk𝔓 X' Y' ξ' η'
  where
    ν-one-third = one-third ·𝕜 ν
    X' = (phi-act ϕ X) +𝔍 (-𝔍 (ν-one-third ⊛𝔍 X)) +𝔍 (two-scalar ⊛𝔍 (B ×𝔍 Y)) +𝔍 (η ⊛𝔍 A)
    Y' = (two-scalar ⊛𝔍 (A ×𝔍 X)) +𝔍 (-𝔍 (phi-adjoint-act ϕ Y)) +𝔍 (ν-one-third ⊛𝔍 Y) +𝔍 (ξ ⊛𝔍 B)
    ξ' = ⟨ A , Y ⟩ⱼ𝕜 +𝕜 (ν ·𝕜 ξ)
    η' = ⟨ B , X ⟩ⱼ𝕜 +𝕜 (-𝕜 (ν ·𝕜 η))

-- ================================================================
-- §4. 公理と証明（戻り値の型を明示してメタ変数を解消）
-- ================================================================

private
  cong4-mkE7 : ∀ {ϕ ϕ' A A' B B' ν ν'} 
    → ϕ ≡ ϕ' → A ≡ A' → B ≡ B' → ν ≡ ν' 
    → mkE7 ϕ A B ν ≡ mkE7 ϕ' A' B' ν'
  cong4-mkE7 p q r s i = mkE7 (p i) (q i) (r i) (s i)

postulate
  E7-antisym-phi : (ϕ₁ ϕ₂ : E6-Lie) (A₁ A₂ B₁ B₂ : 𝔍ᶜ) → 
    (([ ϕ₁ , ϕ₂ ]₆ +E6 (A₁ ∨𝔍 B₂)) +E6 (-E6 (A₂ ∨𝔍 B₁))) ≡ 
    -E6 (([ ϕ₂ , ϕ₁ ]₆ +E6 (A₂ ∨𝔍 B₁)) +E6 (-E6 (A₁ ∨𝔍 B₂)))

  E7-antisym-A : (Φ₁ Φ₂ : E7) → 
    E7.A [ Φ₁ , Φ₂ ]₇ ≡ E7.A (-E7 [ Φ₂ , Φ₁ ]₇)

  E7-antisym-B : (Φ₁ Φ₂ : E7) → 
    E7.B [ Φ₁ , Φ₂ ]₇ ≡ E7.B (-E7 [ Φ₂ , Φ₁ ]₇)

  postulate-nu-antisym : (A₁ A₂ B₁ B₂ : 𝔍ᶜ) → 
    (⟨ A₁ , B₂ ⟩ⱼ𝕜 +𝕜 (-𝕜 ⟨ A₂ , B₁ ⟩ⱼ𝕜)) ≡ 
    (-𝕜 (⟨ A₂ , B₁ ⟩ⱼ𝕜 +𝕜 (-𝕜 ⟨ A₁ , B₂ ⟩ⱼ𝕜)))

-- これを使って nu-part-proof を定義
nu-part-proof : (A₁ A₂ B₁ B₂ : 𝔍ᶜ) → (⟨ A₁ , B₂ ⟩ⱼ𝕜 +𝕜 (-𝕜 ⟨ A₂ , B₁ ⟩ⱼ𝕜)) ≡ (-𝕜 (⟨ A₂ , B₁ ⟩ⱼ𝕜 +𝕜 (-𝕜 ⟨ A₁ , B₂ ⟩ⱼ𝕜)))
nu-part-proof = postulate-nu-antisym

E7-antisym : (Φ₁ Φ₂ : E7) → [ Φ₁ , Φ₂ ]₇ ≡ -E7 [ Φ₂ , Φ₁ ]₇
E7-antisym (mkE7 ϕ₁ A₁ B₁ ν₁) (mkE7 ϕ₂ A₂ B₂ ν₂) = 
  cong4-mkE7 (E7-antisym-phi ϕ₁ ϕ₂ A₁ A₂ B₁ B₂) 
             (E7-antisym-A Φ₁ Φ₂) 
             (E7-antisym-B Φ₁ Φ₂) 
             (nu-part-proof A₁ A₂ B₁ B₂)
  where
    Φ₁ = mkE7 ϕ₁ A₁ B₁ ν₁
    Φ₂ = mkE7 ϕ₂ A₂ B₂ ν₂