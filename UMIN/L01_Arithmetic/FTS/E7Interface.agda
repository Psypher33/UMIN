{-# OPTIONS --cubical --guardedness #-}

module UMIN.L01_Arithmetic.FTS.E7Interface where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; _·_)
open import UMIN.L01_Arithmetic.AlgebraicStructures.FieldOfRationals public
  using (ℚ⁺; _//_; 𝕜; 𝕜-zero; 𝕜-one; _+𝕜_; _·𝕜_; -𝕜_; ratEmbed; posRat)
open import UMIN.L01_Arithmetic.FTS.AlbertAlgebra
  as AlbertAlg using (𝔍ᶜ; mk𝔍; 𝕆-zero; _×𝔍_; _∘_; ⟨_,_⟩ⱼ𝕜; _+𝔍_; _⊛𝔍_; -𝔍_)
open import UMIN.L01_Arithmetic.FTS.E6Interface
  using (E6-Lie; E6-zero; _+E6_; -E6_; _⊛E6_; [_,_]₆; phi-act; phi-adjoint-act; _∨𝔍_;
    τ-E6; λ-E6; τ-E6-inv; λ-E6-inv; τ-λ-E6-comm; B₆-definition)

-- ================================================================
-- §1. 定数と表現空間の定義
-- ================================================================

two-thirds : 𝕜
two-thirds = ratEmbed (posRat 2 3) 𝕜-one

one-third : 𝕜
one-third = ratEmbed (posRat 1 3) 𝕜-one

two-scalar : 𝕜
two-scalar = ratEmbed (posRat 2 1) 𝕜-one

half : 𝕜
half = ratEmbed (posRat 1 2) 𝕜-one

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

-- ================================================================
-- §2.5. E7 クロス積 _×F_ の具体的実装
-- ================================================================
-- 𝔓ᶜ × 𝔓ᶜ → E7
-- P₁ = (X₁, Y₁, ξ₁, η₁), P₂ = (X₂, Y₂, ξ₂, η₂) に対して
-- E7(ϕ, A, B, ν) を構成する

_×F_ : 𝔓ᶜ → 𝔓ᶜ → E7
(mk𝔓 X₁ Y₁ ξ₁ η₁) ×F (mk𝔓 X₂ Y₂ ξ₂ η₂) = mkE7 ϕ-res A-res B-res ν-res
  where
    -- 1. E6 成分: Jordan 導来の和
    -- ϕ = X₁ ∨ Y₂ + X₂ ∨ Y₁
    ϕ-res : E6-Lie
    ϕ-res = (X₁ ∨𝔍 Y₂) +E6 (X₂ ∨𝔍 Y₁)

    -- 2. Albert 代数成分 A: スカラー倍と Jordan クロス積
    -- A = -(1/2)(η₁X₂ + η₂X₁) + Y₁ ×𝔍 Y₂
    A-res : 𝔍ᶜ
    A-res = (half ⊛𝔍 (-𝔍 ((η₁ ⊛𝔍 X₂) +𝔍 (η₂ ⊛𝔍 X₁)))) +𝔍 (Y₁ ×𝔍 Y₂)

    -- 3. Albert 代数成分 B: スカラー倍と Jordan クロス積
    -- B = (1/2)(ξ₁Y₂ + ξ₂Y₁) - X₁ ×𝔍 X₂
    B-res : 𝔍ᶜ
    B-res = (half ⊛𝔍 ((ξ₁ ⊛𝔍 Y₂) +𝔍 (ξ₂ ⊛𝔍 Y₁))) +𝔍 (-𝔍 (X₁ ×𝔍 X₂))

    -- 4. スカラー成分 ν: 内積とスカラーの組み合わせ
    -- ν = -(1/4)(⟨X₁, Y₂⟩ + ⟨X₂, Y₁⟩) + (3/4)(ξ₁η₂ + ξ₂η₁)
    term1 : 𝕜
    term1 = -𝕜 (ratEmbed (posRat 1 4) (⟨ X₁ , Y₂ ⟩ⱼ𝕜 +𝕜 ⟨ X₂ , Y₁ ⟩ⱼ𝕜))
    term2 : 𝕜
    term2 = ratEmbed (posRat 3 4) ((ξ₁ ·𝕜 η₂) +𝕜 (ξ₂ ·𝕜 η₁))
    ν-res : 𝕜
    ν-res = term1 +𝕜 term2

-- ================================================================
-- §2.6. E7 Killing 形式 B₇ の具体的実装
-- ================================================================
-- B₆ は E6Interface で定義済み

-- B₇(Φ₁, Φ₂) = B₆(ϕ₁, ϕ₂) + ⟨A₁, B₂⟩ + ⟨A₂, B₁⟩ + (2/3)ν₁ν₂
-- ※ 係数は UMIN 理論の規格に合わせて調整
B₇-definition : E7 → E7 → 𝕜
B₇-definition (mkE7 ϕ₁ A₁ B₁ ν₁) (mkE7 ϕ₂ A₂ B₂ ν₂) =
  B₆-definition ϕ₁ ϕ₂
  +𝕜 ⟨ A₁ , B₂ ⟩ⱼ𝕜
  +𝕜 ⟨ A₂ , B₁ ⟩ⱼ𝕜
  +𝕜 (two-thirds ·𝕜 (ν₁ ·𝕜 ν₂))

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

-- ================================================================
--  Pᶜ 空間の共役と対合の実装 (E8 Layer4 からの移設)
-- ================================================================

open AlbertAlg using (τ-𝔍; λ-𝔍; τ-𝔍-inv; λ-𝔍-inv; τ-λ-𝔍-comm)

-- 𝕜 の変換 (有理数なので恒等写像)
τ-𝕜 : 𝕜 → 𝕜
τ-𝕜 k = k
λ-𝕜 : 𝕜 → 𝕜
λ-𝕜 k = k

-- 💥 撃破！ Pᶜ 空間の共役と対合の完全実装
τ-P : 𝔓ᶜ → 𝔓ᶜ
τ-P (mk𝔓 X Y ξ η) = mk𝔓 (τ-𝔍 X) (τ-𝔍 Y) (τ-𝕜 ξ) (τ-𝕜 η)

λ-P : 𝔓ᶜ → 𝔓ᶜ
λ-P (mk𝔓 X Y ξ η) = mk𝔓 (λ-𝔍 X) (λ-𝔍 Y) (λ-𝕜 ξ) (λ-𝕜 η)

-- 証明：Pᶜ の対合性 (Albert代数の証明を利用)
private
  cong4-mk𝔓 : ∀ {X X' Y Y' ξ ξ' η η'}
    → X ≡ X' → Y ≡ Y' → ξ ≡ ξ' → η ≡ η'
    → mk𝔓 X Y ξ η ≡ mk𝔓 X' Y' ξ' η'
  cong4-mk𝔓 p1 p2 p3 p4 i = mk𝔓 (p1 i) (p2 i) (p3 i) (p4 i)

τ-P-inv : (P : 𝔓ᶜ) → τ-P (τ-P P) ≡ P
τ-P-inv (mk𝔓 X Y ξ η) = cong4-mk𝔓 (τ-𝔍-inv X) (τ-𝔍-inv Y) refl refl

λ-P-inv : (P : 𝔓ᶜ) → λ-P (λ-P P) ≡ P
λ-P-inv (mk𝔓 X Y ξ η) = cong4-mk𝔓 (λ-𝔍-inv X) (λ-𝔍-inv Y) refl refl

τ-λ-P-comm : (P : 𝔓ᶜ) → τ-P (λ-P P) ≡ λ-P (τ-P P)
τ-λ-P-comm (mk𝔓 X Y ξ η) = cong4-mk𝔓 (τ-λ-𝔍-comm X) (τ-λ-𝔍-comm Y) refl refl

-- ================================================================
--  E7 上の変換の「具体的な実装」と「証明」 (理論武装版)
-- ================================================================

-- 💥 撃破！ E7 レベルの変換の完全実装
-- ϕ (E6), A, B (𝔍ᶜ), ν (𝕜) のそれぞれの変換を呼び出す
τ-E7 : E7 → E7
τ-E7 (mkE7 ϕ A B ν) = mkE7 (τ-E6 ϕ) (τ-𝔍 A) (τ-𝔍 B) (τ-𝕜 ν)

λ-E7 : E7 → E7
λ-E7 (mkE7 ϕ A B ν) = mkE7 (λ-E6 ϕ) (λ-𝔍 A) (λ-𝔍 B) (λ-𝕜 ν)

-- 💥 撃破！ E7 の対合の完全な証明
-- cong4-mkE7 を使い、下位層の証明（τ-𝔍-inv や refl）を詰め込む
τ-E7-inv : (Φ : E7) → τ-E7 (τ-E7 Φ) ≡ Φ
τ-E7-inv (mkE7 ϕ A B ν) = cong4-mkE7 (τ-E6-inv ϕ) (τ-𝔍-inv A) (τ-𝔍-inv B) refl

λ-E7-inv : (Φ : E7) → λ-E7 (λ-E7 Φ) ≡ Φ
λ-E7-inv (mkE7 ϕ A B ν) = cong4-mkE7 (λ-E6-inv ϕ) (λ-𝔍-inv A) (λ-𝔍-inv B) refl

τ-λ-E7-comm : (Φ : E7) → τ-E7 (λ-E7 Φ) ≡ λ-E7 (τ-E7 Φ)
τ-λ-E7-comm (mkE7 ϕ A B ν) = cong4-mkE7 (τ-λ-E6-comm ϕ) (τ-λ-𝔍-comm A) (τ-λ-𝔍-comm B) refl