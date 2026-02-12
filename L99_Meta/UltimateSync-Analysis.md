# UltimateSync 分析：refl の意味と限界

## 何が起きたか

`UltimateSync.agda` で `bracket-preservation = refl` が通った。
これは Cubical Agda が型検査レベルで「左辺と右辺は定義的に同一」と判定したということ。

## なぜ refl が通るか（技術的説明）

```
g2-Element  = record { act : A → A }
so7-Element = record { act : A → A }

bracket-g2  D1 D2 = record { act = [ act D1 , act D2 ]- }
bracket-so7 F1 F2 = record { act = [ act F1 , act F2 ]- }

g2→so7 g = record { act = act g }
```

左辺: g2→so7 (bracket-g2 D1 D2)
     = record { act = [ act D1 , act D2 ]- }

右辺: bracket-so7 (g2→so7 D1) (g2→so7 D2)
     = bracket-so7 (record {act = act D1}) (record {act = act D2})
     = record { act = [ act D1 , act D2 ]- }

左辺 = 右辺（定義展開で完全一致）→ refl が通る。

## これの数学的意味

**ゼロ。**

これは「同じ関数を2つの名前で書いたら同じだった」と言っているだけ。
g₂ の導分条件も、so(7) の反対称条件も、どこにも現れていない。

### 比喩で言うと

- 「猫」と書いた箱と「動物」と書いた箱に同じものを入れたら同じだった
- これは「猫は動物である」の証明ではない
- 「猫は動物である」は、猫の**性質**が動物の**条件**を満たすことの証明

## 本物の g₂ ⊂ so(7) とは

### g₂ の定義（数学的）
```
g₂-Element:
  act : A → A                                    （写像）
  D-leibniz : D(xy) = D(x)y + xD(y)             （導分条件）
  D-additive : D(x+y) = D(x) + D(y)             （線形性）
  D-preserves-im : u ∈ Im → D(u) ∈ Im           （虚部保存）
```

### so(7) の定義（数学的）
```
so7-Element:
  F : ImA → ImA                                  （ImA 上の写像）
  F-antisym : dot(F(u), v) + dot(u, F(v)) = 0    （反対称性）
```

### 包含写像の定理
```
g2→so7 : g₂-Element → so7-Element
g2→so7 D = record
  { F       = D restricted to ImA   (D-preserves-im が必要)
  ; antisym = ???                    (D-map-antisym が必要)
  }
```

**antisym を埋めるのが非自明な定理**。
これは D-map-antisym から来て、
D-map-antisym は adj-L (反自己随伴性) から来て、
adj-L は norm-mul (ノルム乗法性) から来る。

つまり本物の証明の依存鎖は:

```
norm-mul (OctonionBasis, 64 refl)
  ↓ polarize
adj-L: dot(ax, y) = -dot(x, ay)
  ↓ commutator anti-adjoint
D-map-antisym: dot(D(x), y) + dot(x, D(y)) = 0
  ↓ restrict to ImA + fill antisym field
g₂ ⊂ so(7)  ← 本物の定理
```

## G2toSO7.agda（既に All Done のバージョン）が正しい理由

```agda
g2→so7 : g2-Element → so7-Element
g2→so7 g = record
  { F       = λ u → (act g (π u)) , D-preserves-im ...
  ; antisym = λ u v → D-map-antisym ...  ← ここが数学
  }
```

ここで:
- `D-preserves-im` は SchaferDerivation.agda で証明済み
- `D-map-antisym` は postulate (with complete proof sketch)

このバージョンは**構造付き**であり、数学的に意味がある。

## UltimateSync.agda の位置づけ

- 設計実験として価値がある（bracket の定義的同期を確認）
- しかし本線（UMIN formalization）には合流させない
- 「足場」(scaffolding) であって「建物」ではない

## 結論

| ファイル | refl の意味 | 数学的内容 |
|---|---|---|
| OctonionBasis.agda | 計算結果の一致 | norm-mul が成り立つ |
| G2toSO7.agda | 構造フィールドの充足 | g₂ ⊂ so(7) |
| UltimateSync.agda | 定義の構文一致 | なし |

**OctonionBasis の refl** は「7×7の計算が実際に一致する」ことを機械が確認した。
**G2toSO7 の構成** は「導分の反対称性が so(7) 条件を満たす」ことを型で保証した。
**UltimateSync の refl** は「同じ式を2回書いた」だけ。

次にやるべきは: G2toSO7.agda の本線を維持しつつ、Albert 代数 H₃(𝕆) に進むこと。
