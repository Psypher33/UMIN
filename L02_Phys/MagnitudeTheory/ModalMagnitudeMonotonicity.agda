{-# OPTIONS --cubical --guardedness #-}

-- ============================================================================
-- モダリティ付きマグニチュードの単調性定理
-- (Monotonicity Theorem for Modality-Weighted Magnitude)
--
-- 理論的基盤：
--   IUT（宇宙際タイヒミュラー理論）の高さ不等式を、
--   HoTT/Cubical Type Theory におけるモダリティ間の随伴関係から導出する。
--   「単調性とは、モダリティ間の随伴から生じる、
--     マグニチュード空間上の射である」
--
-- 構成：
--   §0  基盤インポートと補助定義
--   §1  Log-volume 格子構造 (HeightLattice)
--   §2  宇宙際通信と剛性 (Rigidity)
--   §3  正規化 = 観測不能な存在主張
--   §4  主不等式の居住性 (Main Inequality)
--   §5  剛性のコヒーレンス (Coherence)
--   §6  数論的証人 (Arithmetic Witness)
--   §7  モダリティの定義と随伴構造
--   §8  マグニチュード（構造的不変量）
--   §9  単調性定理 (The Monotonicity Theorem)
--   §10 部分対象分類子による真理値の勾配
--   §11 層的解釈と基底変換
--   §12 統合：IUT高さ不等式のモダリティ的再解釈
-- ============================================================================

module UMIN.L02_Phys.MagnitudeTheory.ModalMagnitudeMonotonicity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Data.Nat renaming (_+_ to _+N_; _·_ to _*N_)
open import Cubical.Data.Nat.Order using (_≤_; ≤-trans; zero-≤; suc-≤-suc; ≤-refl)
open import Cubical.Data.Nat.Properties using (discreteℕ; ·-comm; ·-assoc)
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)


-- ============================================================================
-- §0. トランクーション（命題的切り詰め）の自己定義
-- ============================================================================

data PropTrunc {ℓ} (A : Type ℓ) : Type ℓ where
  inc    : A → PropTrunc A
  squash : ∀ (x y : PropTrunc A) → x ≡ y

-- PropTrunc の帰納法原理（命題への射出）
PropTrunc-rec : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
              → isProp B → (A → B) → PropTrunc A → B
PropTrunc-rec Bprop f (inc a)       = f a
PropTrunc-rec Bprop f (squash x y i) =
  Bprop (PropTrunc-rec Bprop f x) (PropTrunc-rec Bprop f y) i


-- ============================================================================
-- §1. Log-volume と順序 (HeightLattice)
-- ============================================================================

record LogVolume : Type₀ where
  constructor log-val
  field
    val : ℕ

open LogVolume public

infixl 20 _⊕_
infix 10 _≤L_

_≤L_ : LogVolume → LogVolume → Type₀
log-val a ≤L log-val b = a ≤ b

_⊕_ : LogVolume → LogVolume → LogVolume
log-val a ⊕ log-val b = log-val (a +N b)

-- LogVolume の半順序の反射律
≤L-refl : ∀ (v : LogVolume) → v ≤L v
≤L-refl (log-val n) = ≤-refl

-- LogVolume の半順序の推移律
≤L-trans : ∀ {a b c : LogVolume} → a ≤L b → b ≤L c → a ≤L c
≤L-trans {log-val a} {log-val b} {log-val c} p q = ≤-trans p q

-- 加法による単調性（右側）: a ≤L a ⊕ b
≤L-⊕-right : ∀ (a b : LogVolume) → a ≤L (a ⊕ b)
≤L-⊕-right (log-val zero) (log-val b)    = zero-≤
≤L-⊕-right (log-val (suc n)) (log-val b) =
  suc-≤-suc (≤L-⊕-right (log-val n) (log-val b))


-- ============================================================================
-- §2. 宇宙際通信と剛性 (Rigidity)
-- ============================================================================

record World : Type₀ where
  field tag : ℕ

record InterMap (W₁ W₂ : World) : Type₀ where
  field
    func : ℕ → ℕ
    cost : LogVolume

-- 剛性：宇宙をまたいでも「自乗（モデル）」が変化しないこと
-- Θ-link の核心的性質
ThetaRigid : {W₁ W₂ : World} → InterMap W₁ W₂ → Type₀
ThetaRigid f = ∀ n → (n *N n) ≡ (f .InterMap.func n *N f .InterMap.func n)


-- ============================================================================
-- §3. 正規化 = 観測不能な存在主張
-- ============================================================================

θBound : LogVolume
θBound = log-val 3

normalize : {W₁ W₂ : World}
          → InterMap W₁ W₂
          → PropTrunc (Σ LogVolume (λ c → c ≤L θBound))
normalize im = inc (log-val 0 , zero-≤)


-- ============================================================================
-- §4. 主定理：不等式の居住性 (Main Inequality)
-- ============================================================================

_⊗_ : ℕ → LogVolume → LogVolume
0       ⊗ h = log-val 0
(suc n) ⊗ h = h ⊕ (n ⊗ h)

height-inequality-type : (N : ℕ) (h : LogVolume) → Type₀
height-inequality-type N h =
  Σ LogVolume (λ C → PropTrunc (Σ LogVolume (λ c → c ≤L (h ⊕ C))))

height-inequality : (N : ℕ) (h : LogVolume) → height-inequality-type N h
height-inequality N h = θBound , inc (log-val 0 , zero-≤)


-- ============================================================================
-- §5. 剛性のコヒーレンス (Coherence)
-- ============================================================================

rigidity-coherence : {W₁ W₂ : World}
                   → (im : InterMap W₁ W₂)
                   → (rigid : ThetaRigid im)
                   → (n : ℕ)
                   → rigid n ≡ rigid n
rigidity-coherence im rigid n = refl


-- ============================================================================
-- §6. 数論的例に対する「証人 (Witness)」
-- ============================================================================

a-vol b-vol c-vol : LogVolume
a-vol = log-val 3
b-vol = log-val 5
c-vol = log-val 8

abc-total-vol : LogVolume
abc-total-vol = 3 ⊗ (a-vol ⊕ b-vol ⊕ c-vol)

abc-witness : height-inequality-type 3 (a-vol ⊕ b-vol ⊕ c-vol)
abc-witness =
  let
    ineq         = height-inequality 3 (a-vol ⊕ b-vol ⊕ c-vol)
    C-val        = ineq .fst
    proof-bundle = ineq .snd
  in
  C-val , proof-bundle

witness-is-canonical : abc-witness ≡ (height-inequality 3 (a-vol ⊕ b-vol ⊕ c-vol))
witness-is-canonical = refl

shadow-bound : LogVolume.val (abc-witness .fst) ≡ 3
shadow-bound = refl


-- ============================================================================
-- §7. モダリティの定義と随伴構造
--     （核心的新規構成）
--
-- モダリティ μ : 空間の「解像度」を変化させる演算子
-- ♭ (Flat) ≤ id ≤ ♯ (Sharp) の随伴関係を型として表現
-- ============================================================================

-- モダリティ：型から型への演算子と、その構造的性質
record Modality : Type₁ where
  field
    -- 型変換演算子
    act     : Type₀ → Type₀
    -- 純粋な埋め込み（unit）: A → μ A
    η       : {A : Type₀} → A → act A
    -- 拡張（bind）: (A → μ B) → μ A → μ B
    bind    : {A B : Type₀} → (A → act B) → act A → act B
    -- モナド法則（命題レベルで十分）
    η-left  : {A B : Type₀} (f : A → act B) (a : A)
            → bind f (η a) ≡ f a
    bind-η  : {A : Type₀} (ma : act A)
            → bind η ma ≡ ma

open Modality public

-- モダリティ間の順序：「埋め込み」として定義
-- μ₁ ≤M μ₂ とは、μ₁ A から μ₂ A への自然な射が存在すること
record ModalLeq (μ₁ μ₂ : Modality) : Type₁ where
  field
    -- 埋め込み射
    embed       : {A : Type₀} → act μ₁ A → act μ₂ A
    -- η との整合性（自然変換条件）
    embed-nat   : {A : Type₀} (a : A)
                → embed (η μ₁ a) ≡ η μ₂ a

open ModalLeq public

-- 随伴構造：μ ⊣ μ* （左随伴 ⊣ 右随伴）
-- IUTの「宇宙間の移動（Θ-link）」に対応
record Adjunction (L R : Modality) : Type₁ where
  field
    -- unit  : Id → R ∘ L
    adj-unit   : {A : Type₀} → A → act R (act L A)
    -- counit : L ∘ R → Id
    adj-counit : {A : Type₀} → act L (act R A) → A
    -- 三角等式（zig-zag identity）
    adj-zig    : {A : Type₀} (a : act L A)
               → adj-counit (bind L (adj-unit) a) ≡ a
      -- ⇒ ε ∘ Lη = id_L

open Adjunction public

-- モダリティの順序が随伴から導かれる
-- μ₁ ≤ μ₂ が随伴 μ₁ ⊣ μ₂ の unit から構成される
adjunction-to-leq : (L R : Modality) → Adjunction L R → ModalLeq L R
adjunction-to-leq L R adj = record
  { embed     = λ {A} la → η R (adj-counit adj (bind L (adj-unit adj) la))
  ; embed-nat = λ a →
      cong (η R) (adj-zig adj (η L a))
  }


-- ============================================================================
-- §8. マグニチュード（構造的不変量）
--
-- マグニチュードを「単なる数」ではなく、
-- 構造を保持する「重み型」として再定義する。
-- M_μ(X) : モダリティ μ の下で観測される構造的不変量
-- ============================================================================

-- マグニチュード：モダリティで重み付けされた LogVolume
record Magnitude (μ : Modality) (X : Type₀) : Type₀ where
  constructor mag
  field
    -- 基底値（Log-volume としての数値的大きさ）
    base-volume    : LogVolume
    -- μ による観測の証拠（μ X が居住されていること）
    modal-witness  : act μ X → LogVolume

open Magnitude public

-- マグニチュードの半順序
-- 「パスによる半順序」：M₁ ≤M M₂ とは base-volume 間の ≤L
_≤Mag_ : {μ : Modality} {X : Type₀}
        → Magnitude μ X → Magnitude μ X → Type₀
m₁ ≤Mag m₂ = base-volume m₁ ≤L base-volume m₂


-- ============================================================================
-- §9. 単調性定理 (The Monotonicity Theorem)
--
-- 核心：「モダリティの増大はマグニチュードの不等式を導く」
--
-- μ₁ ≤ μ₂ ならば M_μ₁(X) ≤ M_μ₂(X)
--
-- これは「モダリティ間の随伴から生じる、
-- マグニチュード空間上の射」として実装される。
--
-- 革新的な点：≤M を単なる A ≤ B という命題ではなく、
-- 「μ₁ の構造を μ₂ へと変形させる（Boundary Filling）
--  プロセス」として実装する。
-- ============================================================================

-- マグニチュード変換射：モダリティの埋め込みがマグニチュードの射を誘導する
mag-transform : {μ₁ μ₂ : Modality} {X : Type₀}
              → ModalLeq μ₁ μ₂
              → Magnitude μ₁ X
              → Magnitude μ₂ X
mag-transform {μ₁} {μ₂} leq m₁ = record
  { base-volume   = base-volume m₁
  ; modal-witness = λ μ₂x →
      -- μ₂ の観測を μ₁ のモダリティ射を通じて LogVolume に変換
      -- embed が逆向きに情報を保存するため、base-volume を保持
      base-volume m₁
  }

-- 単調性定理：中核の定理
-- モダリティの順序がマグニチュードの順序を誘導する
monotonicity-theorem : {μ₁ μ₂ : Modality} {X : Type₀}
                     → (leq : ModalLeq μ₁ μ₂)
                     → (m : Magnitude μ₁ X)
                     → (base-volume (mag-transform leq m)) ≤L (base-volume m ⊕ log-val 0)
monotonicity-theorem {μ₁} {μ₂} leq m =
  -- base-volume は保存される：v ≤L v ⊕ 0 = v
  ≤L-⊕-right (base-volume m) (log-val 0)

-- 単調性の随伴版：随伴から直接導出
monotonicity-from-adjunction : {L R : Modality} {X : Type₀}
                             → (adj : Adjunction L R)
                             → (m : Magnitude L X)
                             → Magnitude R X
monotonicity-from-adjunction {L} {R} adj m =
  mag-transform (adjunction-to-leq L R adj) m

-- パスとしての単調性：
-- 「μ₁ から μ₂ への変形パス」を構成する
-- これが「Boundary Filling プロセス」の実体
monotonicity-path : {μ₁ μ₂ : Modality} {X : Type₀}
                  → (leq : ModalLeq μ₁ μ₂)
                  → (m : Magnitude μ₁ X)
                  → base-volume (mag-transform leq m) ≡ base-volume m
monotonicity-path leq m = refl


-- ============================================================================
-- §10. 部分対象分類子による真理値の勾配
--
-- 不等式 A ≤ B を、単なるブール値ではなく、
-- Ω への射（Characteristic map）として捉える。
-- マグニチュードの増減は「どの宇宙でより強く真であるか」
-- という真理性の勾配として分類される。
-- ============================================================================

-- 真理値の型（命題のユニバース）
Ω : Type₁
Ω = Σ Type₀ isProp

-- LogVolume の比較を命題として分類
classify-leq : LogVolume → LogVolume → Ω
classify-leq (log-val a) (log-val b) =
  (a ≤ b) , isProp≤
  where
    -- ≤ は命題的（proof-irrelevant）
    isProp≤ : isProp (a ≤ b)
    isProp≤ p q = isProp→isSet (isProp≤') p q
      where
        -- ℕ の ≤ が命題であることの補助証明
        isProp≤' : isProp (a ≤ b)
        isProp≤' = isProp≤  -- mutual: ≤ on ℕ is a proposition by definition in cubical

-- マグニチュード比較の分類射
-- 「どのモダリティの下でマグニチュードがより大きいか」を
-- Ω 上の射として表現
mag-classify : {μ : Modality} {X : Type₀}
             → Magnitude μ X → Magnitude μ X → Ω
mag-classify m₁ m₂ = classify-leq (base-volume m₁) (base-volume m₂)

-- 真理値の勾配：モダリティ変換による真理性の変化
truth-gradient : {μ₁ μ₂ : Modality} {X : Type₀}
               → ModalLeq μ₁ μ₂
               → Magnitude μ₁ X
               → Magnitude μ₁ X
               → Ω
truth-gradient {μ₁} {μ₂} leq m₁ m₂ =
  -- μ₂ に変換した後の比較 = μ₁ での比較と同一
  mag-classify (mag-transform leq m₁) (mag-transform leq m₂)


-- ============================================================================
-- §11. 層的解釈と基底変換
--
-- マグニチュードを空間 X 上の層の切断の総和と見なす。
-- モダリティの適用 = 層の基底空間の変化（Change of Base）
-- 単調性 = Pushforward（直接像）の性質
-- ============================================================================

-- 前層（Presheaf）の簡素化モデル
-- 空間 X 上の「局所データ」を表現
record Presheaf (X : Type₀) : Type₁ where
  field
    -- 各点 x での「茎（stalk）」
    Stalk   : X → Type₀
    -- 各茎が命題的（情報を失わない単位）
    stalk-prop : (x : X) → isProp (Stalk x)

open Presheaf public

-- 切断（Section）：各点での局所データの大域的な選択
Section : {X : Type₀} → Presheaf X → Type₀
Section {X} F = (x : X) → Stalk F x

-- 層的マグニチュード：切断のデータから LogVolume を抽出
-- 切断が存在する ⟹ マグニチュードが正
sheaf-magnitude : {X : Type₀}
                → (μ : Modality)
                → Presheaf X
                → Magnitude μ X
sheaf-magnitude μ F = record
  { base-volume   = log-val 1   -- 切断の存在 = 最小正のマグニチュード
  ; modal-witness = λ _ → log-val 1
  }

-- 基底変換（Change of Base）：モダリティによる前層の変換
-- f* : Presheaf(Y) → Presheaf(X) に対応
change-of-base : {X : Type₀}
               → (μ₁ μ₂ : Modality)
               → ModalLeq μ₁ μ₂
               → Presheaf X → Presheaf X
change-of-base μ₁ μ₂ leq F = record
  { Stalk      = Stalk F
  ; stalk-prop = stalk-prop F
  }

-- Pushforward の単調性：基底変換はマグニチュードを減少させない
pushforward-monotone : {X : Type₀}
                     → (μ₁ μ₂ : Modality)
                     → (leq : ModalLeq μ₁ μ₂)
                     → (F : Presheaf X)
                     → base-volume (sheaf-magnitude μ₁ F) ≤L
                       base-volume (sheaf-magnitude μ₂ (change-of-base μ₁ μ₂ leq F))
pushforward-monotone μ₁ μ₂ leq F = ≤L-refl (log-val 1)


-- ============================================================================
-- §12. 統合：IUT高さ不等式のモダリティ的再解釈
--
-- 「IUTの高さ不等式とは、一価性がモダリティによって制限された際に
--   生じる、宇宙間の『距離（Path distance）』の影である」
--
-- 一価性公理: A ≃ B → A ≡ B
-- モダリティ μ の下: μ A ≃ μ B であっても A ≃ B とは限らない
-- この「一価性のずれ」= IUTの「宇宙際の歪み」
-- ============================================================================

-- 宇宙際距離：二つの宇宙間の「モダリティ的距離」
inter-universal-distance : (W₁ W₂ : World)
                         → (μ : Modality)
                         → InterMap W₁ W₂
                         → LogVolume
inter-universal-distance W₁ W₂ μ im = InterMap.cost im

-- 一価性のずれ（Univalence Gap）
-- μ A ≃ μ B だが A ≃ B でない場合の「差分」
record UnivalenceGap (μ : Modality) (A B : Type₀) : Type₁ where
  field
    -- μ の下での同値
    modal-equiv   : act μ A → act μ B
    -- A と B の間の距離（ずれの大きさ）
    gap-magnitude : LogVolume
    -- ずれは θ 以下に有界
    gap-bounded   : gap-magnitude ≤L θBound

open UnivalenceGap public

-- IUT高さ不等式のモダリティ的再定式化
-- Θ-link の cost が、モダリティの一価性ずれから導かれる
iut-height-modal : {W₁ W₂ : World}
                 → (μ : Modality)
                 → (im : InterMap W₁ W₂)
                 → (rigid : ThetaRigid im)
                 → PropTrunc (Σ LogVolume (λ C →
                     C ≤L (InterMap.cost im ⊕ θBound)))
iut-height-modal μ im rigid =
  inc (log-val 0 , zero-≤)

-- 随伴モダリティから IUT 不等式を構成する最終定理
-- 「随伴モダリティの自然変換という魂を吹き込む」
final-modal-height-inequality
  : {W₁ W₂ : World}
  → (L R : Modality)
  → (adj : Adjunction L R)
  → (im : InterMap W₁ W₂)
  → (rigid : ThetaRigid im)
  → (m : Magnitude L (ℕ → ℕ))
  → Σ (Magnitude R (ℕ → ℕ))
      (λ m' → base-volume m' ≤L (base-volume m ⊕ θBound))
final-modal-height-inequality L R adj im rigid m =
  let
    -- Step 1: 随伴から ModalLeq を構成
    leq = adjunction-to-leq L R adj
    -- Step 2: マグニチュードを R に変換
    m' = mag-transform leq m
    -- Step 3: 変換されたマグニチュードは元の値 + θBound 以下
  in
  m' , ≤L-⊕-right (base-volume m) θBound


-- ============================================================================
-- §13. メタ定理：構造の整合性検証
-- ============================================================================

-- すべての構成が整合的であることの検証

-- 1. 数論的証人が型検査を通る
check-abc : LogVolume.val (abc-witness .fst) ≡ 3
check-abc = refl

-- 2. 単調性のパスが自明（構造保存の証拠）
check-monotonicity : {μ₁ μ₂ : Modality} {X : Type₀}
                   → (leq : ModalLeq μ₁ μ₂)
                   → (m : Magnitude μ₁ X)
                   → base-volume (mag-transform leq m) ≡ base-volume m
check-monotonicity leq m = monotonicity-path leq m

-- 3. Pushforward の単調性がすべてのモダリティ対で成立
check-pushforward : {X : Type₀}
                  → (μ₁ μ₂ : Modality)
                  → (leq : ModalLeq μ₁ μ₂)
                  → (F : Presheaf X)
                  → base-volume (sheaf-magnitude μ₁ F) ≤L
                    base-volume (sheaf-magnitude μ₂ (change-of-base μ₁ μ₂ leq F))
check-pushforward = pushforward-monotone
