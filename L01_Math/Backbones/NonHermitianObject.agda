{-# OPTIONS --cubical --guardedness --safe #-}

module UMIN.L01_Math.Backbones.NonHermitianObject where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Data.Unit

open import UMIN.L01_Math.Backbones.EmergentJ
open import UMIN.L00_Core.Axiom.TremblingCore
open import UMIN.L00_Core.Logic.SasakiCore
open import UMIN.L00_Core.Logic.SasakiArena

-- ============================================================
-- NonHermitianObject :
--   Trembling/Sasaki arena ＋ EmergentJ の複素構造を束ねた
--   「非エルミート量子オブジェクト」の最初のスケルトン
-- ============================================================

record NonHermitianObject : Type₂ where
  field
    -- 1. 論理・随伴の arena
    arena : QuantumSasakiArena

    -- 2. 実ネットワーク（Z₂ 作用付き状態空間）
    Z     : Z2-Network

    -- 3. 実ネットワークの状態を arena の A へ埋め込む写像
    ι     : Z2-Network.State Z → QuantumSasakiArena.A arena

    -- 4. EmergentPhase Z 上の複素構造（J² = inv）
    complex : ComplexStruct (emergent-inv {Z})

  -- arena / Z の内部構造を外からも見えるようにしておく
  open QuantumSasakiArena arena public
  open Z2-Network Z public

-- ============================================================
-- NonHermitianHom :
--   非エルミートオブジェクト間の「構造保存射」のスケルトン
--   （inv と ι と arena の論理埋め込みの保存）
-- ============================================================

record NonHermitianHom (X Y : NonHermitianObject) : Type₂ where
  open NonHermitianObject X renaming (arena to arenaX; Z to ZX; ι to ιX)
  open NonHermitianObject Y renaming (arena to arenaY; Z to ZY; ι to ιY)

  field
    -- 1. arena の状態空間 A の写像
    mapA :
      QuantumSasakiArena.A arenaX →
      QuantumSasakiArena.A arenaY

    -- 2. 実ネットワークの状態の写像（Z₂ 作用付き）
    mapZ :
      Z2-Network.State ZX →
      Z2-Network.State ZY

    -- 3. Z₂ 作用（inv）を保存
    preserve-inv :
      (x : Z2-Network.State ZX) →
      mapZ (Z2-Network.inv ZX x) ≡
      Z2-Network.inv ZY (mapZ x)

    -- 4. 実ネットワークから arena への埋め込み ι を可換にする
    preserve-ι :
      (x : Z2-Network.State ZX) →
      mapA (ιX x) ≡
      ιY (mapZ x)

    -- 5. arena 内の「状態→命題」写像を「射影」レベルで保存
    --    （QProp 間の写像 mapQ を通して保存する）
    mapQ :
      QuantumSasakiArena.QProp arenaX →
      QuantumSasakiArena.QProp arenaY

    preserve-state-to-prop :
      (a : QuantumSasakiArena.A arenaX) →
      mapQ (QuantumSasakiArena.state-to-prop arenaX a)
      ≡
      QuantumSasakiArena.state-to-prop arenaY (mapA a)

-- ============================================================
-- 圏構造のデータ：恒等射と合成
-- ============================================================

idNH : ∀ {X : NonHermitianObject} → NonHermitianHom X X
idNH {X} = record
  { mapA = λ a → a
  ; mapZ = λ x → x
  ; preserve-inv = λ x → refl
  ; preserve-ι = λ x → refl
  ; mapQ = λ q → q
  ; preserve-state-to-prop = λ a → refl
  }

_∘NH_ :
  {X Y Z : NonHermitianObject} →
  NonHermitianHom Y Z →
  NonHermitianHom X Y →
  NonHermitianHom X Z
_∘NH_ {X} {Y} {Z} g f =
  record
    { mapA = λ a →
        NonHermitianHom.mapA g (NonHermitianHom.mapA f a)
    ; mapZ = λ x →
        NonHermitianHom.mapZ g (NonHermitianHom.mapZ f x)
    ; preserve-inv = λ x →
        cong (NonHermitianHom.mapZ g)
             (NonHermitianHom.preserve-inv f x)
        ∙ NonHermitianHom.preserve-inv g (NonHermitianHom.mapZ f x)
    ; preserve-ι = λ x →
        cong (NonHermitianHom.mapA g)
             (NonHermitianHom.preserve-ι f x)
        ∙ NonHermitianHom.preserve-ι g (NonHermitianHom.mapZ f x)
    ; mapQ = λ q →
        NonHermitianHom.mapQ g (NonHermitianHom.mapQ f q)
    ; preserve-state-to-prop = λ a →
        cong (NonHermitianHom.mapQ g)
             (NonHermitianHom.preserve-state-to-prop f a)
        ∙ NonHermitianHom.preserve-state-to-prop g (NonHermitianHom.mapA f a)
    }

-- ============================================================
-- 単位的な非エルミートオブジェクト（テンソル単位に使う）
-- ============================================================

trivialTC : TremblingCore
trivialTC = record
  { ★       = Unit
  ; isSet-★ = isSetUnit
  ; ext-cert = tt
  }

trivialConn : SasakiConn trivialTC Unit
trivialConn = record
  { s  = λ _ → tt
  ; s† = λ _ → TremblingCore.ext-cert trivialTC
  }

trivialLattice : QuantumLattice
trivialLattice = record
  { QProp   = Unit
  ; _≤_     = λ _ _ → Unit
  ; isProp≤ = λ _ _ → isPropUnit
  ; perp    = λ _ → tt
  ; meet    = λ _ _ → tt
  ; join    = λ _ _ → tt
  ; sasakiAdj = λ p x y → idEquiv _
  }

trivialArena : QuantumSasakiArena
trivialArena = record
  { tc   = trivialTC
  ; A    = Unit
  ; conn = trivialConn
  ; L    = trivialLattice
  ; state-to-prop = λ _ → tt
  ; prop-to-state = λ _ → tt
  ; sasaki-from-conn = λ p a → idEquiv _
  }

trivialZ : Z2-Network
trivialZ = record
  { State   = Unit
  ; inv     = λ x → x
  ; inv-inv = λ x → refl
  }

unitNH : NonHermitianObject
unitNH = record
  { arena   = trivialArena
  ; Z       = trivialZ
  ; ι       = λ x → x
  ; complex = Emergent-Complex-Structure trivialZ
  }


