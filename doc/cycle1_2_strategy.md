# cycle1_hamiltonian / cycle2_hamiltonian 証明戦略

## 0. 現状

- `cycle0_hamiltonian` : 証明完了 (sorry なし)
- `cycle1_hamiltonian` : sorry
- `cycle2_hamiltonian` : sorry
- 残り sorry = 2

---

## 1. 方向関数の比較

### dir0 (証明済み)

| fiber s | 条件 | 方向 |
|:---:|:---:|:---:|
| s=0 | j=m-1 | bumpi |
| s=0 | j<m-1 | bumpk |
| s=m-1 | i>0 | bumpj |
| s=m-1 | i=0 | bumpk |
| mid | i=m-1 | bumpk |
| mid | i<m-1 | **bumpj** |

主方向: bumpj (mid fiber で大半), ブロック: i 座標

### dir1

| fiber s | 条件 | 方向 |
|:---:|:---:|:---:|
| s=0 | (なし) | bumpj |
| s=m-1 | i>0 | bumpk |
| s=m-1 | i=0 | bumpj |
| mid | (なし) | **bumpi** |

主方向: bumpi (mid fiber で無条件), 条件分岐は s=m-1 のみ

### dir2

| fiber s | 条件 | 方向 |
|:---:|:---:|:---:|
| s=0 | j<m-1 | bumpi |
| s=0 | j=m-1 | bumpk |
| s=m-1 | (なし) | bumpi |
| mid | i<m-1 | **bumpk** |
| mid | i=m-1 | bumpj |

主方向: bumpk (mid fiber で大半), ブロック: 要分析

---

## 2. 座標置換の関係（結論: 直接利用不可）

σ₁(i,j,k)=(j,k,i), σ₂(i,j,k)=(k,i,j) として
`dir1(v) = σ⁻¹(dir0(σ(v)))` が成り立つか検証したが、**不成立**。

理由: dir0 の s=0 分岐は j 条件だが、σ 変換後の対応する条件が dir1 の構造と一致しない。

**結論**: 各サイクルを独立に証明する。ただし証明の「テンプレート」（帰納法の骨格、
injectivity→surjectivity 論法、ブロック遷移チェーン）は cycle0 からコピー＆適応できる。

---

## 3. Cycle 1 証明戦略

### 3.1 軌道の1ラウンド (m ステップ) の構造

始点 (i₀, j₀, k₀) (s=0) からの1ラウンド:

| step r | fiber s | 方向 | 到達頂点 |
|:---:|:---:|:---:|:---|
| 0 | 0 | bumpj | (i₀, j₀+1, k₀) |
| 1 | 1 | bumpi | (i₀+1, j₀+1, k₀) |
| 2 | 2 | bumpi | (i₀+2, j₀+1, k₀) |
| ... | ... | bumpi | ... |
| m-2 | m-2 | bumpi | (i₀+m-2, j₀+1, k₀) |
| m-1 | m-1 | (条件) | (下記) |

s=m-1 での i 値 = i₀+m-2:
- i₀+m-2 > 0 (mod m), つまり i₀ ≠ 2: **bumpk** → (i₀+m-2, j₀+1, k₀+1)
- i₀+m-2 = 0 (mod m), つまり i₀ = 2: **bumpj** → (0, j₀+2, k₀)

### 3.2 ラウンド間推移

ラウンド t の始点を (iₜ, jₜ, kₜ) とすると:

- **通常** (iₜ ≠ 2): iₜ₊₁ = iₜ-2, jₜ₊₁ = jₜ+1, kₜ₊₁ = kₜ+1
- **特殊** (iₜ = 2): iₜ₊₁ = 0, jₜ₊₁ = jₜ+2, kₜ₊₁ = kₜ

共通: **iₜ₊₁ = iₜ - 2 (mod m)** (両ケースとも)

gcd(2,m)=1 (m 奇数) なので、m ラウンドで i は全ての値を巡回。

### 3.3 スーパーラウンド (m² ステップ)

m ラウンド後:
- i: i₀ に戻る (Δi = -2m ≡ 0)
- j: +1 × (m-1) + 2 × 1 = **m+1 ≡ 1** (mod m)
- k: +1 × (m-1) + 0 × 1 = **m-1 ≡ -1** (mod m)

m スーパーラウンド後 (= m³ ステップ):
- j: +m ≡ 0, k: -m ≡ 0 → **始点に戻る**

### 3.4 ブロック定義

cycle0 のように単一座標でブロックを定義するのは難しい（1スーパーラウンド内で
i, j, k 全てが変化する）。

**提案**: スーパーラウンド番号 u (0 ≤ u < m) をブロックインデックスとする。

- blockEntry1(u) = スーパーラウンド u の始点
- blockEntry1(0) = start1 (起点)
- blockEntry1(u) = (i₀, j₀+u, k₀-u) where i₀,j₀,k₀ は start1 の座標

**起点の選定**: start1 = (0, m-1, 2) だと s = 0+m-1+2 = m+1 ≡ 1 ≠ 0。
s=0 から始めたいので、 **start1 = (0, 0, 0)** (s=0) を候補とする。
すると blockEntry1(u) = (0, u, m-u) mod m。

### 3.5 Expected 関数

dir1 は条件分岐が1箇所のみなので、Expected 関数は分岐なし（midExpected と同様）
の可能性が高い。

1ラウンド内でのステップ r (0 ≤ r < m) における頂点:

```
dir1Expected(t, r) =
  if r = 0 then (iₜ, jₜ, kₜ)           -- s=0 の始点
  else (iₜ + r - 1, jₜ + 1, kₜ)         -- s=r, bumpi で i が進む
```

ここで iₜ = i₀ - 2t (mod m), jₜ, kₜ はラウンド始点の座標。

**注意**: jₜ, kₜ は t の複雑な関数（特殊ラウンドの位置に依存）。
これを closed-form で書くには、特殊ラウンドが何回目に起こるかを追跡する必要がある。

### 3.6 代替アプローチ: 2段階ブロック

ラウンド単位ではなく、**スーパーラウンド単位** でブロックを定義する方が clean:

```
-- スーパーラウンド u 内のラウンド t、ステップ r での頂点
dir1Expected_full(u, t, r) = ...

-- ブロック完全性: スーパーラウンド u で m² 頂点を網羅
dir1_block_complete(u) : ∀ v with f(v)=u, ∃ n < m², orbit(blockEntry1(u), n) = v
```

スーパーラウンド u 内での i の推移:
- i₀(u) = i₀ - 2 * 0 = i₀ (ラウンド 0)
- iₜ(u) = i₀ - 2t (mod m)

j, k の推移: 特殊ラウンド (iₜ=2) が T 回目に来るとして:
- t < T: jₜ = j₀(u) + t, kₜ = k₀(u) + t
- t = T: jₜ₊₁ = jₜ + 2, kₜ₊₁ = kₜ
- t > T: jₜ = j₀(u) + t + 1, kₜ = k₀(u) + t - 1

特殊ラウンドの位置 T は i₀ - 2T ≡ 2 (mod m) から T = (i₀-2)/2 * 2⁻¹ (mod m)。

**これは複雑すぎる。** もっと良いアプローチを考える。

### 3.7 推奨アプローチ: orbit 帰納法を直接使う

cycle0 と同じ「強帰納法で orbit の n ステップ目を明示公式で表す」方法:

```lean
theorem orbit_dir1_explicit (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3)
    (n : Fin (m ^ 3)) :
    orbit m (dir1 m) start1 n.val = dir1Expected m n := by
  -- 強帰納法 on n
```

**dir1Expected**: n を t*m + r (t=ラウンド番号, r=ラウンド内ステップ) に分解し、
t をさらに u*m + w (u=スーパーラウンド, w=スーパーラウンド内ラウンド) に分解。

しかし 3 重のインデックス管理は証明が煩雑になる。

### 3.8 最終推奨: cycle0 テンプレートの直接適用

**最もシンプルなアプローチ**: cycle0 の証明構造をほぼそのまま踏襲する。

1. **ブロック定義**: j 座標でブロックを定義する
   - 1ラウンド内で j は (j₀ から j₀+1 へ) 1回だけ変化
   - ただし特殊ラウンドで追加の bumpj があるため、j だけではブロックを一意に決められない

   **修正**: (j + k) mod m でブロックを定義する
   - 1ラウンド内: j+k は常に +1 (bumpj で +1 または bumpk で +1)
   - m ステップで j+k が +m ≡ 0 → 1ラウンドで (j+k) mod m は戻る... これは使えない

   **再修正**: i は1ラウンドで m-2 回変化するので不適。

   結局、cycle1 では単一座標によるブロック分割が難しい。
   **スーパーラウンド (m² ステップ) 単位でブロックを定義** し、
   ブロック内の m² 頂点の網羅性を直接示す。

### 3.9 具体的証明計画

```
cycle1_hamiltonian
├── dir1_successor_bijective          [証明済み ✓]
├── orbit_dir1_returns                [要証明] -- m³ ステップで戻る
│   ├── dir1_superround               -- m² ステップ後: j+=1, k-=1, i 不変
│   └── m 回のスーパーラウンドで戻る
├── dir1_orbit_surjective             [要証明] -- 全頂点到達
│   ├── dir1_round_explicit           -- 1ラウンド(m ステップ)の軌道公式
│   │   └── 強帰納法 on r (ラウンド内)
│   ├── dir1_superround_explicit      -- 1スーパーラウンド(m²ステップ)の軌道公式
│   │   └── dir1_round_explicit を m 回適用
│   ├── dir1_superround_complete      -- スーパーラウンド内で m² 頂点網羅
│   │   ├── dir1_expected_injective   -- (t,r) → vertex は単射
│   │   └── Finite.injective_iff_surjective.mp
│   └── dir1_block_transition         -- スーパーラウンド間遷移
└── 全頂点存在の組み立て
```

---

## 4. Cycle 2 証明戦略

### 4.1 dir2 の1ラウンド構造

始点 (i₀, j₀, k₀) (s=0) からの1ラウンド:

| step r | fiber s | 条件 | 方向 | 備考 |
|:---:|:---:|:---:|:---:|:---|
| 0 | 0 | j₀<m-1 | bumpi | i₀→i₀+1 |
| 0 | 0 | j₀=m-1 | bumpk | k₀→k₀+1 |
| 1..m-2 | mid | i<m-1 | bumpk | k 積み上げ |
| 1..m-2 | mid | i=m-1 | bumpj | j 変化 |
| m-1 | m-1 | (なし) | bumpi | i 常に +1 |

dir2 は dir0 と同程度の複雑さ（s=0 と mid に条件分岐あり）。

### 4.2 ラウンド解析

**ケース A: j₀ < m-1** (大半のラウンド)
- Step 0: bumpi → i = i₀+1
- Steps 1..m-2 (mid):
  - i₀+1 < m-1 なら bumpk が m-2 回 → k が m-2 増加
  - i₀+1 = m-1 のとき bumpj（1回だけ、以降 i は変わらないので残りは bumpk）

  実際には step 1 で i = i₀+1 を見て判定。i は変わらない（mid では bumpi しない）ので、
  全 mid ステップで同じ判定結果。
  - i₀+1 < m-1: 全 mid ステップで bumpk → k += m-2
  - i₀+1 = m-1 (i₀ = m-2): 全 mid ステップで bumpj → j += m-2

- Step m-1: bumpi → i += 1

まとめ (j₀ < m-1):
- i₀ ≠ m-2: (i₀+1, j₀, k₀) → mid で bumpk×(m-2) → (i₀+1, j₀, k₀+m-2) → bumpi → **(i₀+2, j₀, k₀+m-2)**
- i₀ = m-2: (m-1, j₀, k₀) → mid で bumpj×(m-2) → (m-1, j₀+m-2, k₀) → bumpi → **(0, j₀+m-2, k₀)**

**ケース B: j₀ = m-1**
- Step 0: bumpk → (i₀, m-1, k₀+1)
- Steps 1..m-2 (mid): i₀ で判定
  - i₀ < m-1: bumpk×(m-2) → k += m-2
  - i₀ = m-1: bumpj×(m-2) → j += m-2
- Step m-1: bumpi → i += 1

まとめ (j₀ = m-1):
- i₀ < m-1: **(i₀+1, m-1, k₀+m-1)** = **(i₀+1, m-1, k₀-1)**
- i₀ = m-1: **(0, m-1+m-2, k₀+1)** = **(0, m-3, k₀+1)** ... 要精査

### 4.3 ブロック構造

dir2 では:
- mid fiber で bumpk が大半 → k が急速に変化
- bumpi は s=0 (j<m-1 時) と s=m-1 で合計最大2回/ラウンド
- bumpj は稀（mid で i=m-1 の時、または s=0 で j=m-1 の時の代替）

cycle0 では「bumpi が稀→ i でブロック分割」だった。
dir2 では bumpi は s=0 (条件付き) と s=m-1 (無条件) で起こるので、
i の変化パターンは cycle0 とは異なるが、**j 座標でブロック分割** できる可能性がある:

- bumpj は mid fiber で i=m-1 の場合のみ（稀）
- ほとんどのラウンドで j は不変

**要精査**: j が変化するのは i₀=m-2 (ケースA) または i₀=m-1 (ケースB) の時のみ。
m ラウンドで j が変化する回数を数える必要がある。

### 4.4 推奨アプローチ

cycle0 と同様の「座標ベースのブロック分割 + orbit 明示公式」を使うが、
ブロックの座標軸を適切に選ぶ必要がある。

dir2 のケース分けの複雑さは dir0 と同程度なので、
**証明量も cycle0 と同程度** (~600-700 行) を見込む。

---

## 5. 実装計画

### 5.1 優先順位

**Cycle 1 を先に証明する** (dir1 の方が単純)。

### 5.2 Cycle 1 実装ステップ

1. **dir1 ヘルパー補題群** (~50 行)
   - `dir1_s0` : s=0 → bumpj
   - `dir1_mid` : 0 < s < m-1 → bumpi
   - `dir1_sm1_pos` : s=m-1, i>0 → bumpk
   - `dir1_sm1_zero` : s=m-1, i=0 → bumpj

2. **blockEntry1 と start1 の定義** (~20 行)
   ```
   start1 = (0, 0, 0)  -- s=0
   blockEntry1(u) = (0, u, m-u) -- スーパーラウンド u の始点
   ```
   ※ 起点は検証が必要。m=3,5 で手計算して確認する。

3. **dir1Expected 定義** (~30 行)
   - ラウンド内の明示公式
   - スーパーラウンド内のラウンド始点公式

4. **ファイバー・座標ヘルパー** (~80 行)
   - `dir1E_fiber` : fiberIndex の計算
   - `dir1E_i`, `dir1E_j_lt` 等

5. **orbit_dir1_explicit** (~200 行)
   - 強帰納法で1スーパーラウンド分を証明
   - base_case + succ_step (mid) + succ_step (s=m-1) + round transition

6. **injectivity / surjectivity** (~100 行)
   - dir1Expected_injective
   - dir1Expected_surjective (via Finite.injective_iff_surjective)

7. **ブロック遷移・返還** (~100 行)
   - dir1_superround_transition
   - orbit_dir1_reaches_block
   - orbit_dir1_returns

8. **cycle1_hamiltonian** (~50 行)
   - 上記を組み立て

**推定合計: ~630 行**

### 5.3 Cycle 2 実装ステップ

Cycle 1 完成後、同様の構造で実装。dir2 の条件分岐が多いため、
ヘルパー補題と orbit explicit の証明がやや長くなる。

**推定合計: ~700 行**

### 5.4 コード再利用

以下は cycle0 から **そのまま再利用可能**:
- `orbit_add`, `orbit_succ`, `orbit_zero`
- `mod_add_raw`, `raw_add_mod`, `mod_add_mod'`
- `fiber_advances`
- `Finite.injective_iff_surjective` パターン
- `zify [show m ≥ 1 from by omega]; ring` パターン (乗法等式)
- `Nat.add_mul_mod_self_left` (n*b の語順に注意)

以下は **テンプレートとしてコピー＆適応**:
- `block_orbit_step` の構造
- `orbit_reaches_block` の帰納法
- `orbit_returns` の計算
- `cycle0_hamiltonian` の最終組み立て

---

## 6. リスクと注意点

1. **blockEntry / Expected の正しい定義を見つけること** が最大のリスク。
   cycle0 では論文の構成から自然に導けたが、cycle1/2 は論文が
   dir0 のみ詳述している可能性がある → 自分で軌道を追って公式を導出する必要。

2. **dir1 の特殊ラウンド** (i₀=2 で bumpj が追加) の処理。
   Expected 関数に if-then-else が必要になるか、
   あるいは closed-form で表現できるかを確認する。

3. **dir2 の二重条件分岐** (s=0 で j 条件 + mid で i 条件) による
   ケース爆発。orbit_explicit の証明が cycle0 より長くなる可能性。

4. **ファイル長**: 現在 ~1910 行。cycle1 (+630) + cycle2 (+700) で
   ~3240 行になる。Lean のコンパイル時間への影響に注意。
   必要に応じてファイル分割を検討。

---

## 7. m=3 での検証トレース

### Cycle 1 (m=3)

起点 (0,0,0), s=0:
```
Step  0: (0,0,0) s=0 bumpj  → (0,1,0)
Step  1: (0,1,0) s=1 bumpi  → (1,1,0)
Step  2: (1,1,0) s=2 bumpk  → (1,1,1)  [i=1>0]
Step  3: (1,1,1) s=0 bumpj  → (1,2,1)
Step  4: (1,2,1) s=1 bumpi  → (2,2,1)
Step  5: (2,2,1) s=2 bumpk  → (2,2,2)  [i=2>0]
Step  6: (2,2,2) s=0 bumpj  → (2,0,2)
Step  7: (2,0,2) s=1 bumpi  → (0,0,2)
Step  8: (0,0,2) s=2 bumpj  → (0,1,2)  [i=0!]
Step  9: (0,1,2) s=0 bumpj  → (0,2,2)
Step 10: (0,2,2) s=1 bumpi  → (1,2,2)
Step 11: (1,2,2) s=2 bumpk  → (1,2,0)  [i=1>0]
Step 12: (1,2,0) s=0 bumpj  → (1,0,0)
Step 13: (1,0,0) s=1 bumpi  → (2,0,0)
Step 14: (2,0,0) s=2 bumpk  → (2,0,1)  [i=2>0]
Step 15: (2,0,1) s=0 bumpj  → (2,1,1)
Step 16: (2,1,1) s=1 bumpi  → (0,1,1)
Step 17: (0,1,1) s=2 bumpj  → (0,2,1)  [i=0!]
Step 18: (0,2,1) s=0 bumpj  → (0,0,1)
Step 19: (0,0,1) s=1 bumpi  → (1,0,1)
Step 20: (1,0,1) s=2 bumpk  → (1,0,2)  [i=1>0]
Step 21: (1,0,2) s=0 bumpj  → (1,1,2)
Step 22: (1,1,2) s=1 bumpi  → (2,1,2)
Step 23: (2,1,2) s=2 bumpk  → (2,1,0)  [i=2>0]
Step 24: (2,1,0) s=0 bumpj  → (2,2,0)
Step 25: (2,2,0) s=1 bumpi  → (0,2,0)
Step 26: (0,2,0) s=2 bumpj  → (0,0,0)  [i=0!]
```

27 = 3³ ステップで全頂点訪問 ✓

ラウンド始点 (s=0 の頂点):
```
Round 0: (0,0,0)  i₀=0
Round 1: (1,1,1)  i₀=1 = 0-2 mod 3
Round 2: (2,2,2)  i₀=2 = 1-2 mod 3  ← 特殊ラウンド
Round 3: (0,1,2)  i₀=0, j+=2, k+=0 (特殊)
Round 4: (1,2,0)  i₀=1
Round 5: (2,0,1)  i₀=2 ← 特殊
Round 6: (0,2,1)  i₀=0
Round 7: (1,0,2)  i₀=1
Round 8: (2,1,0)  i₀=2 ← 特殊
```

スーパーラウンド:
- SR0 (rounds 0-2): 始点 (0,0,0) → 終点の次ラウンド始点 (0,1,2)
  j: 0→1 (+1), k: 0→2 (-1 mod 3) ✓
- SR1 (rounds 3-5): 始点 (0,1,2) → (0,2,1)
  j: 1→2 (+1), k: 2→1 (-1) ✓
- SR2 (rounds 6-8): 始点 (0,2,1) → (0,0,0)
  j: 2→0 (+1), k: 1→0 (-1) ✓

### Cycle 2 (m=3)

起点 (0,0,0), s=0:
```
Step  0: (0,0,0) s=0 j=0<2 bumpi → (1,0,0)
Step  1: (1,0,0) s=1 i=1<2 bumpk → (1,0,1)
Step  2: (1,0,1) s=2        bumpi → (2,0,1)
Step  3: (2,0,1) s=0 j=0<2 bumpi → (0,0,1)
Step  4: (0,0,1) s=1 i=0<2 bumpk → (0,0,2)
Step  5: (0,0,2) s=2        bumpi → (1,0,2)
Step  6: (1,0,2) s=0 j=0<2 bumpi → (2,0,2)
Step  7: (2,0,2) s=1 i=2=m-1 bumpj → (2,1,2)
Step  8: (2,1,2) s=2        bumpi → (0,1,2)
Step  9: (0,1,2) s=0 j=1<2 bumpi → (1,1,2)
Step 10: (1,1,2) s=1 i=1<2 bumpk → (1,1,0)
Step 11: (1,1,0) s=2        bumpi → (2,1,0)
Step 12: (2,1,0) s=0 j=1<2 bumpi → (0,1,0)
Step 13: (0,1,0) s=1 i=0<2 bumpk → (0,1,1)
Step 14: (0,1,1) s=2        bumpi → (1,1,1)
Step 15: (1,1,1) s=0 j=1<2 bumpi → (2,1,1)
Step 16: (2,1,1) s=1 i=2=m-1 bumpj → (2,2,1)
Step 17: (2,2,1) s=2        bumpi → (0,2,1)
Step 18: (0,2,1) s=0 j=2=m-1 bumpk → (0,2,2)
Step 19: (0,2,2) s=1 i=0<2 bumpk → (0,2,0)
Step 20: (0,2,0) s=2        bumpi → (1,2,0)
Step 21: (1,2,0) s=0 j=2=m-1 bumpk → (1,2,1)
Step 22: (1,2,1) s=1 i=1<2 bumpk → (1,2,2)
Step 23: (1,2,2) s=2        bumpi → (2,2,2)
Step 24: (2,2,2) s=0 j=2=m-1 bumpk → (2,2,0)
Step 25: (2,2,0) s=1 i=2=m-1 bumpj → (2,0,0)
Step 26: (2,0,0) s=2        bumpi → (0,0,0)
```

27 ステップで全頂点訪問 ✓

ラウンド始点:
```
Round 0: (0,0,0) j=0 bumpi  → 通常ラウンド
Round 1: (2,0,1) j=0 bumpi  → 通常 (i=2=m-1 → mid で bumpj)
Round 2: (0,0,1) j=0 bumpi  → 通常
Round 3: (2,0,2) j=0 bumpi  → 通常 (i=2=m-1 → mid で bumpj)
Round 4: (0,1,2) j=1 bumpi  → 通常
Round 5: (2,1,0) j=1 bumpi  → 通常 (i=2=m-1)
Round 6: (0,2,1) j=2=m-1 bumpk → 特殊ラウンド
Round 7: (1,2,0) j=2=m-1 bumpk → 特殊
Round 8: (2,2,2) j=2=m-1 bumpk → 特殊
```

観察: j < m-1 のラウンドが先に来て、j = m-1 のラウンドが後に来る。

---

## 8. 結論と次のアクション

1. **Cycle 1 を先に実装** (dir1 の単純さを活用)
2. m=3,5 でのトレースで Expected 関数の closed-form を導出
3. cycle0 のテンプレートに沿って実装
4. Cycle 2 は Cycle 1 完成後に着手
5. 必要に応じてファイル分割 (`ClaudeCycles1.lean`, `ClaudeCycles2.lean`)
