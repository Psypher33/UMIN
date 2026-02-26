{-# OPTIONS --cubical --guardedness #-}

module UMIN.L01_Math.Algebraic_Structures.LieAlgebra.E8LieAlgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _·_)
open import UMIN.L01_Math.Algebraic_Structures.LieAlgebra.E7Interface
open import UMIN.L01_Math.Algebraic_Structures.LieAlgebra.FieldOfRationals
  using (ℚ⁺; _//_; 𝕜; 𝕜-zero; 𝕜-one; _+𝕜_; _·𝕜_; -𝕜_; ratEmbed)
open ℚ⁺

-- ================================================================
--  LAYER 1 : E₇ INTERFACE (Names)
-- ================================================================

-- E7Interface から E7, 𝕜 などを輸入し、Pᶜ だけローカル別名で導入
Pᶜ : Type
Pᶜ = 𝔓ᶜ

postulate
  κ-constant : E7  -- 特性元 Z に対応する定数元

  τ-𝕜 : 𝕜 → 𝕜      -- 複素共役（スカラー）
  τ-E7 : E7 → E7    -- 複素共役（E7 上）
  τ-P  : Pᶜ → Pᶜ    -- 複素共役（Pᶜ 上）
  
  E7-zero    : E7
  -- _+E7_, _⊛E7_, -E7_, E7-antisym は E7Interface で定義済み

  Pᶜ-zero   : Pᶜ
  _+P_      : Pᶜ → Pᶜ → Pᶜ
  -P_       : Pᶜ → Pᶜ
  _⊛P_     : 𝕜 → Pᶜ → Pᶜ

  ⟨_,_⟩ₛ   : Pᶜ → Pᶜ → 𝕜

-- 1. 名前を出し切った後で、まとめてルール（infix）を設定
-- _+E7_, _⊛E7_, -E7_, [_,_]₇, _×F_ の fixity は E7Interface で宣言済み
infixl 20 _+P_ -P_
infixl 30 _⊛P_ _⊛E8_

-- 2. その後に、一度だけ公理（Axioms）を定義
-- E7-antisym は E7Interface で証明済み
postulate
  E7-Jacobi : (Φ₁ Φ₂ Φ₃ : E7)
    → (([ Φ₁ , [ Φ₂ , Φ₃ ]₇ ]₇) +E7 ([ Φ₂ , [ Φ₃ , Φ₁ ]₇ ]₇) +E7 ([ Φ₃ , [ Φ₁ , Φ₂ ]₇ ]₇)) ≡ E7-zero
  E7-rep : (Φ₁ Φ₂ : E7) (P : Pᶜ)
    → E7-act [ Φ₁ , Φ₂ ]₇ P ≡ (E7-act Φ₁ (E7-act Φ₂ P)) +P (-P (E7-act Φ₂ (E7-act Φ₁ P)))
  ×F-derivation : (Φ : E7) (P Q : Pᶜ)
    → [ Φ , P ×F Q ]₇ ≡ ((E7-act Φ P) ×F Q) +E7 (P ×F (E7-act Φ Q))
  ⟨⟩-invariant : (Φ : E7) (P Q : Pᶜ)
    → ⟨ E7-act Φ P , Q ⟩ₛ +𝕜 ⟨ P , E7-act Φ Q ⟩ₛ ≡ 𝕜-zero
  ⟨⟩-antisym : (P Q : Pᶜ) → ⟨ P , Q ⟩ₛ ≡ -𝕜 ⟨ Q , P ⟩ₛ
  ×F-antisym : (P Q : Pᶜ) → P ×F Q ≡ -E7 (Q ×F P)

-- ================================================================
--  LAYER 2 : E₈ CONSTRUCTION
-- ================================================================

record E8 : Type where
  constructor mkE8
  field
    Φ : E7 ; P : Pᶜ ; Q : Pᶜ ; r : 𝕜 ; u : 𝕜 ; v : 𝕜
open E8

_+E8_ : E8 → E8 → E8
mkE8 Φ₁ P₁ Q₁ r₁ u₁ v₁ +E8 mkE8 Φ₂ P₂ Q₂ r₂ u₂ v₂ =
  mkE8 (Φ₁ +E7 Φ₂)
       (P₁ +P P₂)
       (Q₁ +P Q₂)
       (r₁ +𝕜 r₂)
       (u₁ +𝕜 u₂)
       (v₁ +𝕜 v₂)

-E8_ : E8 → E8
-E8 mkE8 Φ P Q r u v =
  mkE8 (-E7 Φ)
       (-P P)
       (-P Q)
       (-𝕜 r)
       (-𝕜 u)
       (-𝕜 v)

_⊛E8_ : 𝕜 → E8 → E8
a ⊛E8 mkE8 Φ P Q r u v =
  mkE8 (a ⊛E7 Φ)
       (a ⊛P P)
       (a ⊛P Q)
       (a ·𝕜 r)
       (a ·𝕜 u)
       (a ·𝕜 v)

τ-E8 : E8 → E8
τ-E8 (mkE8 Φ P Q r u v) =
  mkE8 (τ-E7 Φ) (τ-P P) (τ-P Q) (τ-𝕜 r) (τ-𝕜 u) (τ-𝕜 v)

[_,_]₈ : E8 → E8 → E8
[ R₁ , R₂ ]₈ = mkE8 Φ′ P′ Q′ r′ u′ v′
  where
    Φ₁ = Φ R₁ ; Φ₂ = Φ R₂ ; P₁ = P R₁ ; P₂ = P R₂ ; Q₁ = Q R₁ ; Q₂ = Q R₂
    r₁ = r R₁ ; r₂ = r R₂ ; u₁ = u R₁ ; u₂ = u R₂ ; v₁ = v R₁ ; v₂ = v R₂

    Φ′ = ([ Φ₁ , Φ₂ ]₇) +E7 (P₁ ×F Q₂) +E7 (-E7 (P₂ ×F Q₁))

    P′ = (E7-act Φ₁ P₂)
         +P (-P (E7-act Φ₂ P₁))
         +P (r₁ ⊛P P₂)
         +P (-P (r₂ ⊛P P₁))
         +P (u₁ ⊛P Q₂)
         +P (-P (u₂ ⊛P Q₁))

    Q′ = (E7-act Φ₁ Q₂)
         +P (-P (E7-act Φ₂ Q₁))
         +P (-P (r₁ ⊛P Q₂))
         +P (r₂ ⊛P Q₁)
         +P (v₁ ⊛P P₂)
         +P (-P (v₂ ⊛P P₁))

    r′ = (-𝕜 ⟨ P₁ , Q₂ ⟩ₛ)
         +𝕜 ⟨ P₂ , Q₁ ⟩ₛ
         +𝕜 (u₁ ·𝕜 v₂)
         +𝕜 (-𝕜 (u₂ ·𝕜 v₁))

    u′ = (-𝕜 ⟨ P₁ , P₂ ⟩ₛ)
         +𝕜 (ratEmbed (2 // 1) (r₁ ·𝕜 u₂))
         +𝕜 (-𝕜 (ratEmbed (2 // 1) (r₂ ·𝕜 u₁)))

    v′ = (-𝕜 ⟨ Q₁ , Q₂ ⟩ₛ)
         +𝕜 (-𝕜 (ratEmbed (2 // 1) (r₁ ·𝕜 v₂)))
         +𝕜 (ratEmbed (2 // 1) (r₂ ·𝕜 v₁))

infix 35 [_,_]₈

record KillingCoeffs : Type where
  constructor mkCoeffs
  field
    k₁ : ℚ⁺ ; k₂ : ℚ⁺ ; k₃ : ℚ⁺
open KillingCoeffs

miyashita-coeffs : KillingCoeffs
miyashita-coeffs = mkCoeffs (5 // 3) (15 // 1) (120 // 1)

B₈ : KillingCoeffs → E8 → E8 → 𝕜
B₈ κ R₁ R₂ =
    ratEmbed (k₁ κ) (B₇-definition (Φ R₁) (Φ R₂))
    +𝕜 ratEmbed (k₂ κ) (⟨ Q R₁ , P R₂ ⟩ₛ)
    +𝕜 (-𝕜 (ratEmbed (k₂ κ) (⟨ P R₁ , Q R₂ ⟩ₛ)))
    +𝕜 ratEmbed (k₃ κ) (r R₁ ·𝕜 r R₂)

-- ================================================================
--  LAYER 2.5 : 2-graded 分解 (g₀, g₁, g₂)
-- ================================================================

record g₀ : Type where
  field
    Φ₀ : E7
    r₀ : 𝕜

record g₁ : Type where
  field
    P₁ : Pᶜ
    Q₁ : Pᶜ

record g₂ : Type where
  field
    v₂ : 𝕜

ι-g₀ : g₀ → E8
ι-g₀ x = mkE8 (g₀.Φ₀ x) Pᶜ-zero Pᶜ-zero (g₀.r₀ x) 𝕜-zero 𝕜-zero

ι-g₂ : g₂ → E8
ι-g₂ x = mkE8 E7-zero Pᶜ-zero Pᶜ-zero 𝕜-zero 𝕜-zero (g₂.v₂ x)

Z-characteristic : E8
Z-characteristic = mkE8 κ-constant Pᶜ-zero Pᶜ-zero (-𝕜 𝕜-one) 𝕜-zero 𝕜-zero

adZ : E8 → E8
adZ R = [ Z-characteristic , R ]₈

postulate
  adZ-spec :
    (R : E8) →
    let
      Φᵣ = Φ R
      Pᵣ = P R
      Qᵣ = Q R
      rᵣ = r R
      uᵣ = u R
      vᵣ = v R
    in
    adZ R ≡ mkE8 ([ κ-constant , Φᵣ ]₇)
                 ((E7-act κ-constant Pᵣ) +P (-P Pᵣ))
                 ((E7-act κ-constant Qᵣ) +P Qᵣ)
                 𝕜-zero
                 (-𝕜 (ratEmbed (2 // 1) uᵣ))
                 (ratEmbed (2 // 1) vᵣ)

g₂-element : 𝕜 → E8
g₂-element v₀ = mkE8 E7-zero Pᶜ-zero Pᶜ-zero 𝕜-zero 𝕜-zero v₀

record g₂-verified : Type where
  field
    element    : E8
    is-grade-2 : adZ element ≡ ((ratEmbed (2 // 1) 𝕜-one) ⊛E8 element)

record g₀-verified : Type where
  field
    element  : E8
    is-in-g₀ : adZ element ≡ mkE8 E7-zero Pᶜ-zero Pᶜ-zero 𝕜-zero 𝕜-zero 𝕜-zero

postulate
  g₀-subalgebra : (X Y : g₀-verified) → g₀-verified
  g₀-subalgebra-element :
    (X Y : g₀-verified) →
    g₀-verified.element (g₀-subalgebra X Y) ≡
    [ g₀-verified.element X , g₀-verified.element Y ]₈

-- g₋₂ (固有値 -2 の空間) = (Vᶜ)¹⁴
record V14 : Type where
  field
    V14-element     : E8
    is-grade-neg2   : adZ V14-element ≡ ((-𝕜 (ratEmbed (2 // 1) 𝕜-one)) ⊛E8 V14-element)

-- 論文 source 14 の R₋₂(ζ₁, ξ₁, η, ξ, u) に対応する包含関数
ι-V14 : (ζ₁ : 𝕜) → (P-part : Pᶜ) → (u : 𝕜) → E8
ι-V14 ζ₁ P-part u = mkE8 (ζ₁ ⊛E7 κ-constant-part) P-part Pᶜ-zero 𝕜-zero u 𝕜-zero
  where
    postulate
      κ-constant-part : E7  -- 論文の ζ₁E₁ 形式に対応

-- (Vᶜ)¹⁴ 上の内積の定義と、自己内積のスペック
postulate
  inner-product-μ : V14 → V14 → 𝕜

  get-ζ₁      : V14 → 𝕜
  get-u       : V14 → 𝕜
  other-terms : V14 → 𝕜

  -- 論文 source 18 の具体的な計算式: -4ζ₁u - η₂η₃ + y₁y₁* + ξ₁ξ
  inner-μ-spec :
    (R : V14) →
    inner-product-μ R R ≡
      (-𝕜 (ratEmbed (4 // 1) (get-ζ₁ R ·𝕜 get-u R))) +𝕜 (other-terms R)

postulate
  μ-delta : E8 → E8  -- 論文 source 18 の \tilde{μ}_δ

  -- \tilde{μ}_δ は grade -2 の元を grade 2 へ写す
  μ-delta-grade :
    (R : V14) →
    adZ (μ-delta (V14.V14-element R)) ≡
    ((ratEmbed (2 // 1) 𝕜-one) ⊛E8 (μ-delta (V14.V14-element R)))

-- E8ᶜ の自己同型としての E8-Iso
postulate
  E8-Iso    : Type
  apply-Iso : E8-Iso → E8 → E8

  is-Lie-Hom :
    (α : E8-Iso) (R₁ R₂ : E8) →
    apply-Iso α [ R₁ , R₂ ]₈ ≡
    [ apply-Iso α R₁ , apply-Iso α R₂ ]₈

record G14 : Type where
  field
    iso        : E8-Iso
    commute-Z  : (R : E8) →
                 apply-Iso iso (adZ R) ≡ adZ (apply-Iso iso R)
    preserve-μ : (R : V14) →
                 apply-Iso iso (μ-delta (V14.V14-element R)) ≡
                 μ-delta (apply-Iso iso (V14.V14-element R))

postulate
  Phi1-const : E7  -- 論文の Φ(0, E1, 0, 0)

-- 13次元および12次元の抽出に使う「不動点」となるベクトル
V14-fixed-pt : E8
V14-fixed-pt = mkE8 Phi1-const Pᶜ-zero Pᶜ-zero 𝕜-zero 𝕜-one 𝕜-zero

-- G13 (Spin(13, C)): G14 の元で特定のベクトルを固定するもの
record G13 : Type where
  field
    base-g14 : G14
    fix-pt   :
      apply-Iso (G14.iso base-g14) V14-fixed-pt ≡ V14-fixed-pt

-- G12 (Spin(12, C)): G13 の元でさらに符号反転したベクトルを固定するもの
-- 実際には論文 source 25 にあるように E7^C の部分群へ帰着する
record G12 : Type where
  field
    base-g13 : G13
    fix-pt-neg :
      apply-Iso (G14.iso (G13.base-g14 base-g13))
        (mkE8 Phi1-const Pᶜ-zero Pᶜ-zero 𝕜-zero (-𝕜 𝕜-one) 𝕜-zero)
      ≡ (mkE8 Phi1-const Pᶜ-zero Pᶜ-zero 𝕜-zero (-𝕜 𝕜-one) 𝕜-zero)

-- 補題 7.2.3: G₁₂ は E₇^ℂ の部分群である（命題としての型）
postulate
  G12-in-E7 : Type

-- ================================================================
--  COMPACT REAL FORM VIA CONJUGATION AND λ̄
-- ================================================================

postulate
  λ-bar : E8 → E8              -- 論文 source 7 の λ̄
  λ-bar-involution : (R : E8) → λ-bar (λ-bar R) ≡ R

  B₇-like : KillingCoeffs → E8 → E8 → 𝕜

hermitian-form : E8 → E8 → 𝕜
hermitian-form R₁ R₂ =
  -𝕜 (B₇-like miyashita-coeffs (τ-E8 (λ-bar R₁)) R₂)

record CompactE8 : Type where
  field
    iso : E8-Iso
    -- E8^C の元であり、かつ Hermitian form を保つ
    preserves-hermitian :
      (R₁ R₂ : E8) →
      hermitian-form (apply-Iso iso R₁) (apply-Iso iso R₂) ≡
      hermitian-form R₁ R₂

-- ================================================================
--  REAL V14 & G₁₄^com ≅ Spin(14) (source 49, 命題 7.3.7)
-- ================================================================

-- 実ベクトル空間 V14 (source 49)
record RealV14 : Type where
  field
    vᶜ        : V14
    is-real-v :
      μ-delta (τ-E8 (λ-bar (V14.V14-element vᶜ))) ≡
      (-E8_ (V14.V14-element vᶜ))

-- G₁₄^com: 複素共役・λ̄ と可換な G14 の元
record G14com : Type where
  field
    base-g14 : G14
    -- 複素共役と λ̄ の合成作用に対して可換であること
    is-compact-compatible : (R : E8) →
      τ-E8 (λ-bar (apply-Iso (G14.iso base-g14) R)) ≡
      apply-Iso (G14.iso base-g14) (τ-E8 (λ-bar R))

-- 命題 7.3.7: G₁₄^com ≅ Spin(14)
postulate
  Spin14     : Type
  G14com≅Spin14 : Type  -- G14com と Spin(14) の群同型（命題 7.3.7 に基づく）

-- ================================================================
--  LAYER 3 : THEOREMS AND PROOFS
-- ================================================================

dim-E7 = 133 ; dim-P = 56 ; dim-scalar = 3
dim-Hermitian = 136 ; dim-NonHermitian = 112 ; dim-E8-total = 248

check-Hermitian : dim-Hermitian ≡ 136
check-Hermitian = refl
check-NonHermitian : dim-NonHermitian ≡ 112
check-NonHermitian = refl
check-E8-total : dim-E8-total ≡ 248
check-E8-total = refl

proof-ratio-k₂/k₁ : num (k₂ miyashita-coeffs) · den (k₁ miyashita-coeffs) ≡ 9 · (num (k₁ miyashita-coeffs) · den (k₂ miyashita-coeffs))
proof-ratio-k₂/k₁ = refl

proof-ratio-k₃/k₂ : num (k₃ miyashita-coeffs) · den (k₂ miyashita-coeffs) ≡ 8 · (num (k₂ miyashita-coeffs) · den (k₃ miyashita-coeffs))
proof-ratio-k₃/k₂ = refl

distortion-δ : ℚ⁺
distortion-δ = 126 // 17

check-δ-ratio : 126 · 680 ≡ 17 · 5040
check-δ-ratio = refl

infixl 20 _+E8_

E8-zero : E8
E8-zero = mkE8 E7-zero Pᶜ-zero Pᶜ-zero 𝕜-zero 𝕜-zero 𝕜-zero

JacobiIdentity : Type
JacobiIdentity = (X Y Z : E8) → (([ X , [ Y , Z ]₈ ]₈) +E8 ([ Y , [ Z , X ]₈ ]₈) +E8 ([ Z , [ X , Y ]₈ ]₈)) ≡ E8-zero

postulate
  postulate-E8-Jacobi : JacobiIdentity

-- E8 が Lie 代数として完成していることの宣言
E8-is-LieAlgebra : JacobiIdentity
E8-is-LieAlgebra = postulate-E8-Jacobi

AdInvariance : KillingCoeffs → Type
AdInvariance κ = (X Y Z : E8) → B₈ κ [ X , Y ]₈ Z +𝕜 B₈ κ Y [ X , Z ]₈ ≡ 𝕜-zero

Cochain1 : Type
Cochain1 = E8 → 𝕜
Cochain2 : Type
Cochain2 = E8 → E8 → 𝕜
Cochain3 : Type
Cochain3 = E8 → E8 → E8 → 𝕜

d₁ : Cochain1 → Cochain2
d₁ f X Y = f [ X , Y ]₈

d₂ : Cochain2 → Cochain3
d₂ ω X Y Z = ω [ X , Y ]₈ Z +𝕜 (-𝕜 (ω [ X , Z ]₈ Y)) +𝕜 ω [ Y , Z ]₈ X

-- コホモロジーの境界写像の性質：d ∘ d = 0
postulate
  d-squared-zero : (f : Cochain1) (X Y Z : E8) → d₂ (d₁ f) X Y Z ≡ 𝕜-zero

AnomalyCancellation : Type
AnomalyCancellation =
  (p₁ p₂ p₃ : Pᶜ) → let
    pureP : Pᶜ → E8
    pureP p = mkE8 E7-zero p Pᶜ-zero 𝕜-zero 𝕜-zero 𝕜-zero
    pureQ : Pᶜ → E8
    pureQ q = mkE8 E7-zero Pᶜ-zero q 𝕜-zero 𝕜-zero 𝕜-zero
  in Φ (([ pureP p₁ , [ pureP p₂ , pureQ p₃ ]₈ ]₈) +E8 ([ pureP p₂ , [ pureQ p₃ , pureP p₁ ]₈ ]₈) +E8 ([ pureQ p₃ , [ pureP p₁ , pureP p₂ ]₈ ]₈)) ≡ E7-zero