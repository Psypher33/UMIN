{-# OPTIONS --cubical --safe --guardedness #-}

module UMIN.L01_Math.Arithmetic_Universes.Alienation where

-- 1. ここでライブラリを読み込む（これで Type や isSet が使えるようになる）
open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.SetTruncation as ST

-- ================================================================
-- 2. 抽象理論のための内部モジュール
--    ここで Label 等をパラメータとして受け取る
-- ================================================================
module Theory
  (Label : Type)            -- Type₀ の代わりに Type を使用（Cubicalの標準）
  (isSetLabel : isSet Label)
  (ℓ_base : Label)
  (ℓ_obs  : Label)
  where

  -- ================================================================
  -- 3. 宇宙の構造と剛性
  -- ================================================================

  record Universe (ℓ : Label) : Type₁ where
    field
      Structure : Type      -- Type₀ は Type と書くのが一般的
      Core      : Type
      -- ST.rec を使うために、Core が集合(Set)である証明が必要
      isSetCore : isSet Core 
      getCore   : Structure → Core

  -- 剛性（Coricity）の定義
  -- リンクを通じても「核」の情報が保存されることを保証する
  record Coricity (ℓ₁ ℓ₂ : Label) (U₁ : Universe ℓ₁) (U₂ : Universe ℓ₂) 
                  (f : Universe.Structure U₁ → Universe.Structure U₂) : Type where
    field
      isoCore : Universe.Core U₁ ≃ Universe.Core U₂
      is-coric : (s : Universe.Structure U₁) → 
                 Universe.getCore U₂ (f s) ≡ equivFun isoCore (Universe.getCore U₁ s)

  -- ================================================================
  -- 4. Θ-リンクと不確定性（Indeterminacy）
  -- ================================================================

  -- 戻り値を Type (Type₀) に設定
  ThetaLinkRel : (ℓ₁ ℓ₂ : Label) (U₁ : Universe ℓ₁) (U₂ : Universe ℓ₂) → Type
  ThetaLinkRel ℓ₁ ℓ₂ U₁ U₂ = 
    Universe.Structure U₁ → ST.∥ Universe.Structure U₂ ∥₂

  -- UMIN-Link：剛性と不確定性の統合
  record UMIN-Link (ℓ₁ ℓ₂ : Label) : Type₁ where
    field
      U₁ : Universe ℓ₁
      U₂ : Universe ℓ₂
      link : ThetaLinkRel ℓ₁ ℓ₂ U₁ U₂
      
      -- 【重要】剛性のために、Core間の同型を保持する
      isoCore : Universe.Core U₁ ≃ Universe.Core U₂

      -- 剛性の制約：
      -- 多値的な link の出力(ST)を Core に射影すると、
      -- isoCore で移した結果と一致しなければならない。
      rigidity : (s₁ : Universe.Structure U₁) → 
                 ST.rec (Universe.isSetCore U₂) 
                        (λ s₂ → Universe.getCore U₂ s₂) 
                        (link s₁)
                 ≡ equivFun isoCore (Universe.getCore U₁ s₁)