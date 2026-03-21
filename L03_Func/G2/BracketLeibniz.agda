{-# OPTIONS --safe --cubical --guardedness #-}

------------------------------------------------------------------------
-- UMIN OUROBOROS PROJECT
-- Module: UMIN.L03_Func.G2.BracketLeibniz
--
-- --safe 完全版
--
-- 全補題を AltAlgebra の公理のみから導出:
--   +assoc, +comm, +invR, +idL, ldist, rdist
--     → inv-unique      逆元の一意性
--     → neg-distrib     -(x+y) = (-x)+(-y)   ← makeAbGroup 不使用
--     → zero-mul-r/l    0v·c = 0v
--     → neg-mul-r/l     (-a)·c = -(a·c)
--     → cancel-cross-terms
--     → bracket-leibniz [✓]
--
-- 残存 postulate: なし
-- フラグ: --safe --cubical --guardedness
------------------------------------------------------------------------

module UMIN.L03_Func.G2.BracketLeibniz where

open import Cubical.Foundations.Prelude

------------------------------------------------------------------------
-- §1. AltAlgebra
------------------------------------------------------------------------

record AltAlgebra (V : Type₀) : Type₁ where
  infixl 30 _·_
  infixl 20 _+_
  field
    _·_       : V → V → V
    left-alt  : ∀ x y → (x · x) · y ≡ x · (x · y)
    right-alt : ∀ x y → x · (y · y) ≡ (x · y) · y
    _+_    : V → V → V
    0v     : V
    -_     : V → V
    +assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
    +comm  : ∀ x y   → x + y ≡ y + x
    +invR  : ∀ x     → x + (- x) ≡ 0v
    +idL   : ∀ x     → 0v + x ≡ x
    ldist  : ∀ x y z → x · (y + z) ≡ x · y + x · z
    rdist  : ∀ x y z → (x + y) · z ≡ x · z + y · z

  -- ----------------------------------------------------------------
  -- 基本派生補題
  -- ----------------------------------------------------------------

  +idR : ∀ x → x + 0v ≡ x
  +idR x = +comm x 0v ∙ +idL x

  +invL : ∀ x → (- x) + x ≡ 0v
  +invL x = +comm (- x) x ∙ +invR x

  -- ----------------------------------------------------------------
  -- inv-unique: z + w ≡ 0v → z ≡ - w
  -- 逆元の一意性（全導出の基盤）
  -- ----------------------------------------------------------------
  inv-unique : ∀ (z w : V) → z + w ≡ 0v → z ≡ - w
  inv-unique z w zw=0 =
    sym (+idR z)
    ∙ cong (z +_) (sym (+invR w))
    ∙ sym (+assoc z w (- w))
    ∙ cong (_+ (- w)) zw=0
    ∙ +idL (- w)

  -- ----------------------------------------------------------------
  -- neg-distrib: -(x+y) ≡ (-x)+(-y)
  --
  -- 証明: inv-unique ((-x)+(-y)) (x+y) を使う
  --   ((-x)+(-y)) + (x+y)
  --   = (-x) + ((-y)+(x+y))      [+assoc]
  --   = (-x) + (((-y)+x)+y)      [+assoc]
  --   = (-x) + ((x+(-y))+y)      [+comm]
  --   = (-x) + (x+((-y)+y))      [+assoc]
  --   = (-x) + (x+0v)            [+invL]
  --   = (-x) + x                 [+idR]
  --   = 0v                        [+invL]
  --
  -- makeAbGroup 不使用 → --safe 対応
  -- ----------------------------------------------------------------
  neg-distrib : ∀ x y → - (x + y) ≡ (- x) + (- y)
  neg-distrib x y =
    sym (inv-unique ((- x) + (- y)) (x + y)
      ( +assoc (- x) (- y) (x + y)
      ∙ cong ((- x) +_)
          ( sym (+assoc (- y) x y)
          ∙ cong (_+ y) (+comm (- y) x)
          ∙ +assoc x (- y) y
          ∙ cong (x +_) (+invL y)
          ∙ +idR x )
      ∙ +invL x ))

  -- ----------------------------------------------------------------
  -- zero-mul-r: 0v · c ≡ 0v
  --
  -- dup: (0v·c)+(0v·c) ≡ 0v·c
  --   = sym (rdist 0v 0v c) ∙ cong(_·c)(+idL 0v)
  --
  -- main: x+x=x → x=0v パターン
  --   0v·c
  --   = 0v·c + 0v                    [sym +idR]
  --   = 0v·c + (0v·c + (-(0v·c)))   [sym +invR]
  --   = (0v·c + 0v·c) + (-(0v·c))   [sym +assoc]
  --   = 0v·c + (-(0v·c))            [dup]
  --   = 0v                           [+invR]
  -- ----------------------------------------------------------------
  zero-mul-r : ∀ (c : V) → 0v · c ≡ 0v
  zero-mul-r c =
    let dup : (0v · c) + (0v · c) ≡ 0v · c
        dup = sym (rdist 0v 0v c) ∙ cong (_· c) (+idL 0v)
    in sym (+idR (0v · c))
       ∙ cong ((0v · c) +_) (sym (+invR (0v · c)))
       ∙ sym (+assoc (0v · c) (0v · c) (- (0v · c)))
       ∙ cong (_+ (- (0v · c))) dup
       ∙ +invR (0v · c)

  -- ----------------------------------------------------------------
  -- zero-mul-l: c · 0v ≡ 0v
  -- ----------------------------------------------------------------
  zero-mul-l : ∀ (c : V) → c · 0v ≡ 0v
  zero-mul-l c =
    let dup : (c · 0v) + (c · 0v) ≡ c · 0v
        dup = sym (ldist c 0v 0v) ∙ cong (c ·_) (+idL 0v)
    in sym (+idR (c · 0v))
       ∙ cong ((c · 0v) +_) (sym (+invR (c · 0v)))
       ∙ sym (+assoc (c · 0v) (c · 0v) (- (c · 0v)))
       ∙ cong (_+ (- (c · 0v))) dup
       ∙ +invR (c · 0v)

  -- ----------------------------------------------------------------
  -- neg-mul-r: (- a) · c ≡ - (a · c)
  --
  -- 証明: inv-unique ((-a)·c) (a·c)
  --   ((-a)·c) + (a·c)
  --   = ((-a)+a)·c    [sym rdist]
  --   = 0v·c          [+invL]
  --   = 0v            [zero-mul-r]
  -- ----------------------------------------------------------------
  neg-mul-r : ∀ (a c : V) → (- a) · c ≡ - (a · c)
  neg-mul-r a c =
    inv-unique ((- a) · c) (a · c)
      ( sym (rdist (- a) a c)
      ∙ cong (_· c) (+invL a)
      ∙ zero-mul-r c )

  -- ----------------------------------------------------------------
  -- neg-mul-l: b · (- d) ≡ - (b · d)
  --
  -- 証明: inv-unique (b·(-d)) (b·d)
  --   (b·(-d)) + (b·d)
  --   = b·((-d)+d)    [sym ldist]
  --   = b·0v          [+invL]
  --   = 0v            [zero-mul-l]
  -- ----------------------------------------------------------------
  neg-mul-l : ∀ (b d : V) → b · (- d) ≡ - (b · d)
  neg-mul-l b d =
    inv-unique (b · (- d)) (b · d)
      ( sym (ldist b (- d) d)
      ∙ cong (b ·_) (+invL d)
      ∙ zero-mul-l b )

------------------------------------------------------------------------
-- §2. IsDer
------------------------------------------------------------------------

record IsDer {V : Type₀} (A : AltAlgebra V) (D : V → V) : Type₀ where
  open AltAlgebra A
  field
    D-add     : ∀ x y → D (x + y) ≡ D x + D y
    D-leibniz : ∀ x y → D (x · y) ≡ D x · y + x · D y

------------------------------------------------------------------------
-- §3. 主補題群
------------------------------------------------------------------------

module BracketLeibnizProof
  {V   : Type₀}
  (A   : AltAlgebra V)
  {D₁ D₂ : V → V}
  (der₁   : IsDer A D₁)
  (der₂   : IsDer A D₂)
  where

  open AltAlgebra A
  open IsDer der₁ renaming (D-leibniz to lz₁ ; D-add to add₁)
  open IsDer der₂ renaming (D-leibniz to lz₂ ; D-add to add₂)

  --------------------------------------------------------------------
  -- expand-D₁D₂  [✓]
  --------------------------------------------------------------------

  expand-D₁D₂ : ∀ x y
    → D₁ (D₂ (x · y))
    ≡ (D₁ (D₂ x) · y + D₂ x · D₁ y) + (D₁ x · D₂ y + x · D₁ (D₂ y))
  expand-D₁D₂ x y =
    cong D₁ (lz₂ x y)
    ∙ add₁ (D₂ x · y) (x · D₂ y)
    ∙ cong₂ _+_ (lz₁ (D₂ x) y) (lz₁ x (D₂ y))

  --------------------------------------------------------------------
  -- expand-D₂D₁  [✓]
  --------------------------------------------------------------------

  expand-D₂D₁ : ∀ x y
    → D₂ (D₁ (x · y))
    ≡ (D₂ (D₁ x) · y + D₁ x · D₂ y) + (D₂ x · D₁ y + x · D₂ (D₁ y))
  expand-D₂D₁ x y =
    cong D₂ (lz₁ x y)
    ∙ add₂ (D₁ x · y) (x · D₁ y)
    ∙ cong₂ _+_ (lz₂ (D₁ x) y) (lz₂ x (D₁ y))

  --------------------------------------------------------------------
  -- cancel-cross-terms  [✓]
  --------------------------------------------------------------------

  private
    absorb-l : ∀ (x y : V) → x + ((- x) + y) ≡ y
    absorb-l x y =
      sym (+assoc x (- x) y)
      ∙ cong (_+ y) (+invR x)
      ∙ +idL y

  cancel-cross-terms : ∀ (P Q R S P' S' : V)
    → ((P + Q) + (R + S)) + (- ((P' + R) + (Q + S')))
    ≡ (P + (- P')) + (S + (- S'))

  cancel-cross-terms P Q R S P' S' =

    -- Step A: neg展開
    cong (((P + Q) + (R + S)) +_)
      ( neg-distrib (P' + R) (Q + S')
      ∙ cong₂ _+_ (neg-distrib P' R) (neg-distrib Q S') )

    ∙ -- Step B: R と (-R) を消去
      ( let rest = (- Q) + (- S')
            elim-R : (R + S) + (((- P') + (- R)) + rest)
                   ≡ (- P') + (S + rest)
            elim-R =
              sym (+assoc (R + S) ((- P') + (- R)) rest)
              ∙ cong (_+ rest)
                  ( +assoc R S ((- P') + (- R))
                  ∙ cong (R +_)
                      ( sym (+assoc S (- P') (- R))
                      ∙ cong (_+ (- R)) (+comm S (- P'))
                      ∙ +assoc (- P') S (- R) )
                  ∙ sym (+assoc R (- P') (S + (- R)))
                  ∙ cong (_+ (S + (- R))) (+comm R (- P'))
                  ∙ +assoc (- P') R (S + (- R))
                  ∙ cong ((- P') +_)
                      ( cong (R +_) (+comm S (- R))
                      ∙ sym (+assoc R (- R) S)
                      ∙ cong (_+ S) (+invR R)
                      ∙ +idL S ) )
              ∙ +assoc (- P') S rest
        in
        +assoc (P + Q) (R + S) (((- P') + (- R)) + rest)
        ∙ cong ((P + Q) +_) elim-R )

    ∙ -- Step C: Q と (-Q) を消去
      sym (+assoc (P + Q) (- P') (S + ((- Q) + (- S'))))
      ∙ cong (_+ (S + ((- Q) + (- S'))))
          ( +assoc P Q (- P')
          ∙ cong (P +_) (+comm Q (- P'))
          ∙ sym (+assoc P (- P') Q) )
      ∙ +assoc (P + (- P')) Q (S + ((- Q) + (- S')))
      ∙ cong ((P + (- P')) +_)
          ( cong (Q +_)
              ( sym (+assoc S (- Q) (- S'))
              ∙ cong (_+ (- S')) (+comm S (- Q))
              ∙ +assoc (- Q) S (- S') )
          ∙ absorb-l Q (S + (- S')) )

  --------------------------------------------------------------------
  -- bracket-leibniz  [✓]
  --------------------------------------------------------------------

  bracket-leibniz : ∀ x y
    → (D₁ (D₂ (x · y)) + (- (D₂ (D₁ (x · y)))))
    ≡ (D₁ (D₂ x) + (- (D₂ (D₁ x)))) · y
    + x · (D₁ (D₂ y) + (- (D₂ (D₁ y))))

  bracket-leibniz x y =
    let
      P  : V ; P  = D₁ (D₂ x) · y
      Q  : V ; Q  = D₂ x · D₁ y
      R  : V ; R  = D₁ x · D₂ y
      S  : V ; S  = x · D₁ (D₂ y)
      P' : V ; P' = D₂ (D₁ x) · y
      S' : V ; S' = x · D₂ (D₁ y)
    in
    -- Step 1: Leibniz則で8項に展開
    cong₂ (λ u v → u + (- v))
      (expand-D₁D₂ x y)
      (expand-D₂D₁ x y)

    -- Step 2: 交差項を消去
    ∙ cancel-cross-terms P Q R S P' S'

    -- Step 3: 分配則を逆適用
    ∙ sym
        ( cong₂ (λ u v → u + v)
            ( rdist (D₁ (D₂ x)) (- (D₂ (D₁ x))) y
            ∙ cong (P +_) (neg-mul-r (D₂ (D₁ x)) y) )
            ( ldist x (D₁ (D₂ y)) (- (D₂ (D₁ y)))
            ∙ cong (S +_) (neg-mul-l x (D₂ (D₁ y))) ) )

------------------------------------------------------------------------
-- §4. アノテーション表（--safe 完全版）
------------------------------------------------------------------------

-- Component              Status  使用補題
-- ─────────────────────────────────────────────────────────────────────
-- +idR                    [✓]    +comm, +idL
-- +invL                   [✓]    +comm, +invR
-- inv-unique              [✓]    +idR, +invR, +assoc, +idL
-- neg-distrib             [✓]    inv-unique, +assoc, +comm, +invL, +idR
--                                ← makeAbGroup 不使用
-- zero-mul-r              [✓]    rdist, +idL, +idR, +invR, +assoc
-- zero-mul-l              [✓]    ldist, +idL, +idR, +invR, +assoc
-- neg-mul-r               [✓]    rdist, +invL, zero-mul-r, inv-unique
-- neg-mul-l               [✓]    ldist, +invL, zero-mul-l, inv-unique
-- absorb-l (private)      [✓]    +assoc, +invR, +idL
-- expand-D₁D₂             [✓]    lz₂, add₁, lz₁
-- expand-D₂D₁             [✓]    lz₁, add₂, lz₂
-- cancel-cross-terms      [✓]    neg-distrib, absorb-l, +assoc, +comm
-- bracket-leibniz         [✓]    expand-*, cancel-cross-terms,
--                                 rdist, ldist, neg-mul-r, neg-mul-l
-- ─────────────────────────────────────────────────────────────────────
-- 追加 import: なし（Cubical.Foundations.Prelude のみ）
-- 追加 field:  なし
-- 残存 postulate: なし
-- フラグ: --safe --cubical --guardedness
------------------------------------------------------------------------