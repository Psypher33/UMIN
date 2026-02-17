{-# OPTIONS --cubical --safe --guardedness #-}

module UMIN.L00_Core.Logic.UMIN_Theorem where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat as ℕ using (ℕ)

-- ================================================================
-- 🚀 HoTT的アプローチ：逆元の存在を型で表現
-- ================================================================

-- ある元 x が、ある元 y の「乗法逆元」であるという性質（命題付きデータ）
isInvertible : (Carrier : Type) (_*_ : Carrier → Carrier → Carrier) (one : Carrier) (y : Carrier) → Type
isInvertible Carrier _*_ one y = Σ Carrier (λ inv → (y * inv) ≡ one)

-- ================================================================
-- 🚀 UMINを「2が可逆な可換環」として一般化
-- ================================================================

record UMIN-Algebra : Type₁ where
  field
    Carrier : Type
    zero one : Carrier
    _+_ _*_ _-_ : Carrier → Carrier → Carrier
    
    -- 可換環の基本公理
    +-assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
    +-comm  : ∀ a b → a + b ≡ b + a
    +-inverse-cancelˡ : ∀ a b c → (a + b) - (a + c) ≡ b - c
    +-inverse-cancelʳ : ∀ a b c → (a + c) - (b + c) ≡ a - b
    
    *-assoc : ∀ a b c → (a * b) * c ≡ a * (b * c)
    *-distribʳ : ∀ a b c → (a + b) * c ≡ (a * c) + (b * c)
    *-distribˡ : ∀ a b c → a * (b + c) ≡ (a * b) + (a * c)
    *-identityˡ : ∀ a → one * a ≡ a
    *-identityʳ : ∀ a → a * one ≡ a
    
    -- HoTTの極意：この宇宙では「1+1 (つまり2) には逆元が存在する」と宣言する
    two-is-invertible : isInvertible Carrier _*_ one (one + one)

  -- 💡 導出される概念
  two : Carrier
  two = one + one

  half : Carrier
  half = fst two-is-invertible

  half-prop : two * half ≡ one
  half-prop = snd two-is-invertible

  half+half=one : half + half ≡ one
  half+half=one = 
    cong₂ _+_ (sym (*-identityˡ half)) (sym (*-identityˡ half))
    ∙ sym (*-distribʳ one one half)
    ∙ half-prop

  quarter : Carrier
  quarter = half * half

  half-is-2quarters : half ≡ quarter + quarter
  half-is-2quarters = 
    sym (*-identityʳ half)
    ∙ cong (λ x → half * x) (sym half+half=one)
    ∙ *-distribˡ half half half

-- ================================================================
-- 🚀 抽象理論の構築（有理数に一切依存しない、絶対不変の真理）
-- ================================================================

module AbstractTheory (A : UMIN-Algebra) where
  open UMIN-Algebra A

  record AlphaState : Type where
    constructor mkState
    field
      L A₁ D : Carrier

  measure : AlphaState → Carrier
  measure (mkState L A₁ D) = L + (A₁ + D)

  Assoc : AlphaState → AlphaState → AlphaState → Carrier
  Assoc s₁ s₂ s₃ = 
    let L₁ = AlphaState.L s₁; A₁ = AlphaState.A₁ s₁; D₁ = AlphaState.D s₁
        L₂ = AlphaState.L s₂; A₂ = AlphaState.A₁ s₂; D₂ = AlphaState.D s₂
        L₃ = AlphaState.L s₃; A₃ = AlphaState.A₁ s₃; D₃ = AlphaState.D s₃
        
        L-lhs = (L₁ + L₂) + L₃ ; A-lhs = (A₁ + A₂) + A₃
        D-lhs = (((D₁ + D₂) * half) + D₃) * half
        
        L-rhs = L₁ + (L₂ + L₃) ; A-rhs = A₁ + (A₂ + A₃)
        D-rhs = (D₁ + ((D₂ + D₃) * half)) * half
        
    in (L-lhs + (A-lhs + D-lhs)) - (L-rhs + (A-rhs + D-rhs))

  -- 各種キャンセル補題
  LA-cancel : ∀ (l a d₁ d₂ : Carrier) → (l + (a + d₁)) - (l + (a + d₂)) ≡ d₁ - d₂
  LA-cancel l a d₁ d₂ = 
    cong₂ _-_ (sym (+-assoc l a d₁)) (sym (+-assoc l a d₂))
    ∙ +-inverse-cancelˡ (l + a) d₁ d₂

  D-expand-lhs : ∀ (d₁ d₂ d₃ : Carrier) → (((d₁ + d₂) * half) + d₃) * half 
                 ≡ (d₁ * quarter) + ((d₂ * quarter) + (d₃ * half))
  D-expand-lhs d₁ d₂ d₃ = 
    *-distribʳ (((d₁ + d₂) * half)) d₃ half
    ∙ cong (λ x → x + (d₃ * half)) (
        *-assoc (d₁ + d₂) half half
        ∙ *-distribʳ d₁ d₂ quarter
      )
    ∙ +-assoc (d₁ * quarter) (d₂ * quarter) (d₃ * half)

  D-expand-rhs : ∀ (d₁ d₂ d₃ : Carrier) → (d₁ + ((d₂ + d₃) * half)) * half 
                 ≡ (d₁ * half) + ((d₂ * quarter) + (d₃ * quarter))
  D-expand-rhs d₁ d₂ d₃ = 
    *-distribʳ d₁ ((d₂ + d₃) * half) half
    ∙ cong (λ x → (d₁ * half) + x) (
        *-assoc (d₂ + d₃) half half
        ∙ *-distribʳ d₂ d₃ quarter
      )

  final-cancel : ∀ (q1 q3 : Carrier) → 
    (q1 + (q3 + q3)) - ((q1 + q1) + q3) ≡ q3 - q1
  final-cancel q1 q3 = 
    let x = q1 + q3 in
    cong₂ _-_ 
      (sym (+-assoc q1 q3 q3))
      (+-assoc q1 q1 q3 ∙ cong (λ y → q1 + y) (+-comm q1 q3) ∙ sym (+-assoc q1 q3 q1))
    ∙ +-inverse-cancelˡ x q3 q1

  -- 🛡️ 抽象環上の主定理（100%安全完走）
  main-theorem : ∀ (s₁ s₂ s₃ : AlphaState)
    → Assoc s₁ s₂ s₃ ≡ (AlphaState.D s₃ * quarter) - (AlphaState.D s₁ * quarter)
  main-theorem (mkState L₁ A₁ D₁) (mkState L₂ A₂ D₂) (mkState L₃ A₃ D₃) = 
    let d-lhs = (((D₁ + D₂) * half) + D₃) * half
        d-rhs = (D₁ + ((D₂ + D₃) * half)) * half
        L-sum = (L₁ + L₂) + L₃ ; A-sum = (A₁ + A₂) + A₃
        q1 = D₁ * quarter ; q2 = D₂ * quarter ; q3 = D₃ * quarter
    in 
      Assoc (mkState L₁ A₁ D₁) (mkState L₂ A₂ D₂) (mkState L₃ A₃ D₃)
      
      -- 1. RHS の L と A の結合法則を LHS に合わせて消去準備
      ≡⟨ cong (λ x → (L-sum + (A-sum + d-lhs)) - (x + ((A₁ + (A₂ + A₃)) + d-rhs))) (sym (+-assoc L₁ L₂ L₃)) ⟩
      (L-sum + (A-sum + d-lhs)) - (L-sum + ((A₁ + (A₂ + A₃)) + d-rhs))
      ≡⟨ cong (λ x → (L-sum + (A-sum + d-lhs)) - (L-sum + (x + d-rhs))) (sym (+-assoc A₁ A₂ A₃)) ⟩
      (L-sum + (A-sum + d-lhs)) - (L-sum + (A-sum + d-rhs))
      
      -- 2. LA-cancel 適用
      ≡⟨ LA-cancel L-sum A-sum d-lhs d-rhs ⟩
      (d-lhs - d-rhs)
      
      -- ★ ここが形を厳密に合わせた修正箇所です！
      -- 3. D の展開（D-expand-lhs の出力である右結合の形をそのまま書く）
      ≡⟨ cong₂ _-_ (D-expand-lhs D₁ D₂ D₃) (D-expand-rhs D₁ D₂ D₃) ⟩
      (q1 + (q2 + (D₃ * half))) - ((D₁ * half) + (q2 + q3))
      
      -- 4. パズル：D2*quarter (つまり q2) を端に寄せて消す
      -- まず左辺（lhs）の q2 を右端に寄せる
      ≡⟨ cong (λ x → x - ((D₁ * half) + (q2 + q3))) (cong (λ y → q1 + y) (+-comm q2 (D₃ * half)) ∙ sym (+-assoc q1 (D₃ * half) q2)) ⟩
      ((q1 + (D₃ * half)) + q2) - ((D₁ * half) + (q2 + q3))
      
      -- 次に右辺（rhs）の q2 を右端に寄せ、D1*half と q3 も入れ替える
      ≡⟨ cong (λ x → ((q1 + (D₃ * half)) + q2) - x) (cong (λ y → (D₁ * half) + y) (+-comm q2 q3) ∙ sym (+-assoc (D₁ * half) q3 q2) ∙ cong (λ y → y + q2) (+-comm (D₁ * half) q3)) ⟩
      ((q1 + (D₃ * half)) + q2) - (((q3 + (D₁ * half)) + q2))
      
      -- これで完璧に q2 が右端に揃ったので消去！
      ≡⟨ +-inverse-cancelʳ (q1 + (D₃ * half)) (q3 + (D₁ * half)) q2 ⟩
      (q1 + (D₃ * half)) - (q3 + (D₁ * half))
      
      -- 5. half を quarter + quarter に分解
      ≡⟨ cong₂ _-_ (cong (λ x → q1 + (D₃ * x)) half-is-2quarters) (cong (λ x → q3 + (D₁ * x)) half-is-2quarters) ⟩
      (q1 + (D₃ * (quarter + quarter))) - (q3 + (D₁ * (quarter + quarter)))
      
      -- 6. 分配法則
      ≡⟨ cong₂ _-_ (cong (λ x → q1 + x) (*-distribˡ D₃ quarter quarter)) (cong (λ x → q3 + x) (*-distribˡ D₁ quarter quarter)) ⟩
      (q1 + (q3 + q3)) - (q3 + (q1 + q1))
      
      -- 7. 最終消去（final-cancelの形に合わせる）
      ≡⟨ cong (λ x → (q1 + (q3 + q3)) - x) (+-comm q3 (q1 + q1)) ⟩
      (q1 + (q3 + q3)) - ((q1 + q1) + q3)
      ≡⟨ final-cancel q1 q3 ⟩
      q3 - q1
    ∎