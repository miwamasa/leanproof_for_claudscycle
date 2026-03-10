# Claude's Cycles 形式化：中間報告
**Lean 4 / Mathlib v4.29.0-rc2**
**対象論文**: Don Knuth, "Claude's Cycles" (28 Feb 2026; revised 02 Mar 2026)

---

## 1. 問題設定

### グラフの定義

$m^3$ 個の頂点 $(i, j, k)$（$0 \le i, j, k < m$、つまり $\mathbb{Z}/m\mathbb{Z}$ の三つ組）からなる有向グラフを考える。

各頂点から 3 本の弧が出る：
$$
(i,j,k) \xrightarrow{\text{bumpi}} (i{+}1,j,k), \quad
(i,j,k) \xrightarrow{\text{bumpj}} (i,j{+}1,k), \quad
(i,j,k) \xrightarrow{\text{bumpk}} (i,j,k{+}1)
$$
（加算はすべて $\bmod m$）

### 命題

> **奇数 $m \ge 3$** のとき、全 $3m^3$ 本の弧を **3 本のハミルトン $m^3$-サイクル** に分解できる。

Knuth の構成では、各頂点で 3 方向のうちどれを「Cycle 0 用」「Cycle 1 用」「Cycle 2 用」に割り当てるかを**明示的な方向関数** `dir0`, `dir1`, `dir2` で与える。

---

## 2. 基本定義（Lean コード対応）

```
Vertex m  :=  Fin m × Fin m × Fin m

fiberIndex m v  :=  v.1 + v.2.1 + v.2.2   -- s = (i+j+k) mod m  (: Fin m)

bump m v d  :=  d 方向の座標を +1 (mod m) した頂点

successor m dirFn v  :=  bump m v (dirFn v)

orbit m dirFn start n  :=  start から n ステップ進んだ頂点
```

### ファイバーインデックス $s = (i+j+k) \bmod m$ の役割

- **どの方向にバンプしても** $s$ は $+1 \pmod m$ される（`fiber_advances`）。
- したがって軌道上の頂点は $s$ の値ごとに「層（ファイバー）」を形成し、
  $s = 0 \to 1 \to 2 \to \cdots \to m{-}1 \to 0 \to \cdots$ の順に巡回する。
- この周期性が証明の骨格を与える。

---

## 3. 方向関数の定義

### dir0（Cycle 0 用）

| ファイバー $s$ | 座標条件 | 選ばれる方向 |
|:---:|:---:|:---:|
| $s = 0$ | $j = m{-}1$ | **bumpi** |
| $s = 0$ | $j < m{-}1$ | bumpk |
| $s = m{-}1$ | $i > 0$ | bumpj |
| $s = m{-}1$ | $i = 0$ | bumpk |
| $0 < s < m{-}1$ | $i = m{-}1$ | bumpk |
| $0 < s < m{-}1$ | $i < m{-}1$ | **bumpj** |

### dir1（Cycle 1 用）

| $s$ | 条件 | 方向 |
|:---:|:---:|:---:|
| $s = 0$ | — | bumpj |
| $s = m{-}1$ | $i > 0$ | bumpk |
| $s = m{-}1$ | $i = 0$ | bumpj |
| $0 < s < m{-}1$ | — | **bumpi** |

### dir2（Cycle 2 用）

| $s$ | 条件 | 方向 |
|:---:|:---:|:---:|
| $s = 0$ | $j < m{-}1$ | bumpi |
| $s = 0$ | $j = m{-}1$ | bumpk |
| $s = m{-}1$ | — | **bumpi** |
| $0 < s < m{-}1$ | $i < m{-}1$ | bumpk |
| $0 < s < m{-}1$ | $i = m{-}1$ | bumpj |

**置換性**: `directions_are_permutation` で証明済み。各頂点で `{dir0 v, dir1 v, dir2 v} = {bumpi, bumpj, bumpk}` が成立し、各弧はちょうど 1 つのサイクルに属す。

---

## 4. 証明の全体スケッチ

最終目標 `claude_decomposition` の証明は以下の 4 段階からなる。

```
claude_decomposition
├── cycle0_hamiltonian          [sorry: §8.2]
├── cycle1_hamiltonian          [sorry: §8.2]
├── cycle2_hamiltonian          [sorry: §8.2]
└── directions_are_permutation  [proved ✓]
```

### Cycle 0 のハミルトン性（最も詳細に形式化中）

Cycle 0 のハミルトン性証明は以下の構造を持つ：

```
cycle0_hamiltonian
├── successor_dir0_bijective    [proved ✓]  -- successor は全単射
├── block_exit_bumps_i          [proved ✓]  -- ブロック境界で i が+1される
├── i0_block_complete           [proved ✓ (modulo orbit_i0_explicit)]
│   ├── i0Expected_surjective   [proved ✓]
│   │   └── i0Expected_jk_injective  [proved ✓]
│   │       ├── jbase_add_kbase      [proved ✓]
│   │       └── mul2_bijective_odd   [proved ✓]
│   └── orbit_i0_explicit       [sorry §8.1] ←── 現在の主目標
│       ├── i0E_fiber           [prove 中: neg case でコンパイルエラー]
│       ├── i0E_j_lt            [sorry §8.1]
│       └── base_case_i0        [proved ✓]
└── last_block_complete         [proved ✓ (modulo orbit_last_explicit)]
    ├── lastExpected_surjective [proved ✓]
    │   └── lastExpected_jk_injective [proved ✓]
    └── orbit_last_explicit     [sorry §8.1] ←── 現在の主目標
```

---

## 5. 定理・補題の依存関係詳細

### 5.1 証明済み（sorry なし）

| 定理・補題名 | 内容 | 依存先 |
|:--|:--|:--|
| `fiber_advances` | $s$ が各ステップで $+1$ | — |
| `directions_are_permutation` | 3方向が置換を成す | — |
| `bump_injective` | バンプは単射 | — |
| `successor_dir0_injective` | dir0 の後続関数は単射 | `bump_injective`, `fiber_advances`, `dir0_*` 系 |
| `successor_dir0_bijective` | dir0 の後続関数は全単射 | `successor_dir0_injective` |
| `successor_dir1_injective/bijective` | 同上（dir1） | 同様の構造 |
| `successor_dir2_injective/bijective` | 同上（dir2） | 同様の構造 |
| `mul2_bijective_odd` | $x \mapsto 2x$ は全単射 ($m$ 奇数) | `Nat.Coprime`, `dvd_of_dvd_mul_left` |
| `cycle0_i_change_condition` | bumpi iff $s=0$ and $j=m{-}1$ | — |
| `block_exit_bumps_i` | ブロック境界で bumpi | `cycle0_i_change_condition` |
| `jbase_add_kbase` | $j_b + k_b = 1$ in $\text{Fin}\ m$ | 基本算術 |
| `t_eq_of_kbase_eq` | $k_b$ 一致 $\Rightarrow$ $t$ 一致 | `mul2_bijective_odd` |
| `i0Expected_jk_injective` | $(t,r) \mapsto (j,k)$ は単射 | `jbase_add_kbase`, `t_eq_of_kbase_eq` |
| `i0Expected_surjective` | i0Expected は $\{0\} \times \text{Fin}^2$ を被覆 | `i0Expected_jk_injective`, `Finite.injective_iff_surjective` |
| `lastExpected_jk_injective` | 同上（lastExpected） | `jbase_add_kbase`, `mul2_bijective_odd` |
| `lastExpected_surjective` | lastExpected は $\{m{-}1\} \times \text{Fin}^2$ を被覆 | `lastExpected_jk_injective` |
| `i0_block_complete` | $i=0$ ブロック完全訪問 | `i0Expected_surjective`, **`orbit_i0_explicit` (sorry)** |
| `last_block_complete` | $i=m{-}1$ ブロック完全訪問 | `lastExpected_surjective`, **`orbit_last_explicit` (sorry)** |
| `base_case_i0` | 軌道の初期値確認 | 算術計算 |
| `i0E_i` | i0Expected の i 成分 = 0 | — |
| `i0E_fiber` | i0Expected のファイバー計算 | **neg case: コンパイルエラー残存** |
| `checkpoints0_injective` | checkpoint0 は単射 | `mul2_bijective_odd` |
| `orbit_succ`, `orbit_zero` | 軌道の基本等式 | — |
| `orbit_fiber_step` | 軌道のファイバーが $+1$ | `fiber_advances` |
| `successor_bumpj/k/i` | 特定方向の後続関数の明示的な形 | — |
| 各 `dir0_*` 補題 | dir0 の場合分け補題群 | — |
| 各 mod 算術補題 | `mod_add_raw`, `raw_add_mod` 等 | 基本算術 |

### 5.2 未証明（sorry: 7 件）

| 定理名 | 内容 | 依存される定理 | 証明戦略 |
|:--|:--|:--|:--|
| `i0E_fiber` (neg case) | i0Expected のファイバー = 0 の証明（`r=m-1` 分岐） | `orbit_i0_explicit` | $\text{Fin}$ 算術の `dsimp` + `rw` チェーン修正 |
| `i0E_j_lt` | $j < m{-}1$ の境界条件 | `orbit_i0_explicit` | $m$ 奇数 + 矛盾証明 |
| `orbit_i0_explicit` | $i=0$ ブロックの軌道の明示公式 | `i0_block_complete` | 帰納法（`t*m+r` の強帰納） |
| `i0Expected_injective` | i0Expected は単射（**未使用**） | なし | 削除可能 |
| `orbit_last_explicit` | $i=m{-}1$ ブロックの軌道の明示公式 | `last_block_complete` | 同上（dir0 の bumpk/j で構造が変わる） |
| `cycle0_hamiltonian` | Cycle 0 のハミルトン性 | `claude_decomposition` | ブロック完全性 + ブロック遷移の組合せ |
| `cycle1_hamiltonian` | Cycle 1 のハミルトン性 | `claude_decomposition` | dir1 の構造解析 |
| `cycle2_hamiltonian` | Cycle 2 のハミルトン性 | `claude_decomposition` | dir2 の構造解析 |

---

## 6. 明示的軌道公式：`i0Expected` と `lastExpected`

### 6.1 i0Expected（$i = 0$ ブロック）

ラウンド $t \in \{0, \ldots, m{-}1\}$、ステップ $r \in \{0, \ldots, m{-}1\}$ における頂点：

$$
j_{\rm base}(t) = (2m - 1 - 2t) \bmod m, \quad k_{\rm base}(t) = (2 + 2t) \bmod m
$$

$$
\text{i0Expected}(t, r) = \begin{cases}
(0,\ j_b + r,\ k_b) & r \le m{-}2 \\
(0,\ j_b + (m{-}2),\ k_b + 1) & r = m{-}1
\end{cases}
$$

- ファイバー: $r \le m{-}2$ のとき $s = 1 + r$、$r = m{-}1$ のとき $s = 0$（`i0E_fiber`）
- $i = 0$（`i0E_i`）
- $j_b + k_b = 1 \in \text{Fin}\ m$（`jbase_add_kbase`）
- ラウンドごとに $(j_b, k_b)$ は 2 ずつシフト → $\gcd(2, m) = 1$ から全 $k$ 値を網羅

### 6.2 lastExpected（$i = m{-}1$ ブロック）

$$
\text{lastExpected}(t, r) = \begin{cases}
(m{-}1,\ j_b,\ k_b + r) & r \le m{-}2 \\
(m{-}1,\ j_b + 1,\ k_b + (m{-}2)) & r = m{-}1
\end{cases}
$$

- 中間ファイバーでは $i = m{-}1$ なので bumpk が選ばれ、$k$ が積み上がる（i0Expected の $j$ 方向と対称）

### 6.3 `orbit_i0_explicit` の証明戦略

**主張**: `orbit m (dir0 m) start₀ (t*m + r) = i0Expected m t r`

**証明手順**（未完）:

```
強帰納法 on n = t*m + r:
  基底: n=0 → base_case_i0 ✓

  中間ファイバー (r ≤ m-3, t 任意):
    仮定: orbit[n] = (0, j_b + r, k_b)
    dir0 の確認: s = 1+r (中間) かつ i=0 (i<m-1) → dir0 = bumpj
    結論: orbit[n+1] = (0, j_b + (r+1), k_b) = i0Expected(t, r+1) ✓

  ラウンド末 (r = m-2):
    仮定: orbit[n] = (0, j_b + (m-2), k_b)
    dir0 の確認: s = m-1 かつ i=0 → dir0 = bumpk  [dir0_sm1_i0]
    結論: orbit[n+1] = (0, j_b + (m-2), k_b + 1) = i0Expected(t, m-1) ✓

  ラウンド遷移 (r = m-1 → r=0 of next round):
    仮定: orbit[n] = (0, j_b + (m-2), k_b + 1)
    dir0 の確認: s = 0, j = j_b + (m-2)
      → j ≠ m-1 (← i0E_j_lt が必要!!) → dir0 = bumpk  [dir0_s0_jlt]
    結論: orbit[n+1] = (0, j_b + (m-2), k_b + 2)
           = (0, j_b(t+1), k_b(t+1)) [← 算術計算]
           = i0Expected(t+1, 0) ✓
```

**`i0E_j_lt` の証明戦略**:
主張: $j_b(t) + (m{-}2) < m{-}1$ (i.e., $j_{\rm base}(t) < 1$, i.e., $j_b(t) = 0$)
Wait, actually: the claim is that at $r = m{-}1$, the vertex $(0, j_b + (m{-}2), k_b + 1)$ has $j < m{-}1$.
$j = j_b + (m{-}2) = (2m{-}1{-}2t + m{-}2) \bmod m = (3m{-}3{-}2t) \bmod m$.
We need $(3m{-}3{-}2t) \bmod m \ne m{-}1$, i.e., $m \nmid (3m{-}3{-}2t{-}(m{-}1)) = 2m{-}2{-}2t = 2(m{-}1{-}t)$.
Since $1 \le t+1 \le m{-}1$, we have $1 \le m{-}1{-}t \le m{-}2$, so $2 \le 2(m{-}1{-}t) \le 2(m{-}2)$.
If $m \mid 2(m{-}1{-}t)$ and $m$ is odd, then $m \mid (m{-}1{-}t)$ (since $\gcd(2,m)=1$), but $1 \le m{-}1{-}t \le m{-}2 < m$, 矛盾。

---

## 7. 証明過程で浮上した技術的課題

### 7.1 Fin 算術の rw チェーン

`Fin m` の加算は `(a + b).val = (a.val + b.val) % m` という形式で表現される。証明中に複数の `%m` がネストすると、`rw` のパターンマッチが失敗しやすい。

**確立した手順**:
1. `unfold` または `dsimp only [Fin.val_add, Fin.val_mk]` で Nat レベルに降りる
2. `Fin.coe_ofNat_eq_mod` で数値リテラル `(1 : Fin m).val` を `1 % m` に変換
3. `mod_add_raw` / `← Nat.add_mod` で `%m` をフラット化（`conv` で内側を先に処理）
4. `omega` + `Nat.mul_mod_right` 等で算術的結論を得る

**教訓**: `ring` や `abel` は `Fin m` では使えない（内部的に `omega` を呼ぶが Fin の型変換で失敗）。`dsimp only [Fin.val_mk]` だけでは数値リテラルの `.val` が展開されない（`Fin.coe_ofNat_eq_mod` も要る）。

### 7.2 mod 算術補題のライブラリ

以下の補題群を `private theorem` として定義して共用している：

| 補題名 | 主張 |
|:--|:--|
| `mod_add_raw a b m` | `(a % m + b) % m = (a + b) % m` |
| `raw_add_mod a b m` | `(a + b % m) % m = (a + b) % m` |
| `mod_add_mod' a b m` | `(a % m + b % m) % m = (a + b) % m` |
| `val_add_mod a b n` | `(a + b % n) % n = (a + b) % n` |

### 7.3 単射性 → 全射性の論法

`Fin m × Fin m`（有限集合）上の関数について、単射性から全射性を自動的に導く `Finite.injective_iff_surjective.mp` を多用している。これにより `i0Expected_surjective` や `lastExpected_surjective` を単射性の証明から得ている。

---

## 8. 残タスクと優先度

### 8.1 直近（orbit 公式の完成）

**優先度 HIGH**:

1. **`i0E_fiber` neg case のコンパイルエラー修正**
   現在のエラー: `rw [← Nat.add_mod]` のパターンマッチ失敗
   対処: `conv_lhs => arg 1; arg 1; rw [mod_add_raw]` の後、`← Nat.add_mod` を使う

2. **`i0E_j_lt` の証明**
   戦略: $m \mid 2(m{-}1{-}t)$ かつ $m$ 奇数 → $m \mid (m{-}1{-}t)$ → $1 \le m{-}1{-}t < m$ と矛盾
   使用補題: `mul2_bijective_odd` の単射性 or `Nat.Coprime.dvd_of_dvd_mul_left`

3. **`orbit_i0_explicit` の証明**
   戦略: 上記 §6.3 の帰納法（`t*m+r` の強帰納）
   必要補題: `i0E_fiber`, `i0E_j_lt`, `dir0_sm1_i0`, `dir0_s0_jlt`

4. **`orbit_last_explicit` の証明**
   構造は `orbit_i0_explicit` と対称（$j$ と $k$ の役割が入れ替わる）

### 8.2 その後（ハミルトン性の完成）

**優先度 MEDIUM**:

5. **`cycle0_hamiltonian`**
   ブロック完全性（`i0_block_complete`, `last_block_complete`）+ ブロック遷移（`block_exit_bumps_i`）を組み合わせて $m$ ブロック × $m^2$ 頂点 = $m^3$ 頂点を網羅

6. **`cycle1_hamiltonian`, `cycle2_hamiltonian`**
   dir1, dir2 についても同様の構造を形式化

### 8.3 整理・削除

- **`i0Expected_injective`** は現在 `sorry` のままだが、`i0Expected_jk_injective` があれば十分なので削除可能

---

## 9. 現在のビルド状態

```
ビルドジョブ: 3108 件
コンパイルエラー: 1 件（i0E_fiber の neg case）
sorry 件数: 7 件（i0E_fiber, i0E_j_lt, orbit_i0_explicit,
                   i0Expected_injective, orbit_last_explicit,
                   cycle0/1/2_hamiltonian）
```

### sorry の依存ツリー（葉から根へ）

```
i0E_fiber [neg case エラー]
    ↓
i0E_j_lt [sorry]
    ↓
orbit_i0_explicit [sorry] ──────────────────────────────┐
                                                         ↓
orbit_last_explicit [sorry] ──────────────────> cycle0_hamiltonian [sorry]
                                                         ↓
i0Expected_injective [sorry, 未使用]         cycle1_hamiltonian [sorry]
                                                         ↓
                                             cycle2_hamiltonian [sorry]
                                                         ↓
                                          claude_decomposition [sorry 依存]
```

`orbit_i0_explicit` と `orbit_last_explicit` の 2 件を証明できれば、その下にある `i0_block_complete`、`last_block_complete` が自動的に確定し、`cycle0_hamiltonian` の証明に大きく近づく。

---

## 10. ファイル構成

| ファイル | 内容 | 行数 |
|:--|:--|:--|
| `ClaudeCycles.lean` | 主定義・主定理 | ~955 行 |
| `Lemmas.lean` | 補助証明・$m=3$ 検証 | ~170 行 |
| `doc/intermediate_paper.md` | 本文書（中間報告） | — |
| `証明解説.md` | 旧版ドキュメント（初期段階） | — |
| `lakefile.toml` | Lake ビルド設定 | — |
| `lean-toolchain` | `leanprover/lean4:v4.29.0-rc2` | — |

---

## 付録：`dir0` 方向関数の動作と軌道の直感

$m = 5$ のとき、$i = 0$ ブロック（$i = 0$ の全 $25$ 頂点）における軌道を追うと：

- **ラウンド $t = 0$**: $j_b = 4, k_b = 2$
  $s=1$ で bumpj → $s=2$ で bumpj → $\cdots$ → $s=4$ で bumpk（$i=0$ なので）→ $s=0$
  訪問: $(0,4,2), (0,0,2), (0,1,2), (0,2,2), (0,3,2) \to (0,3,3)$

- **ラウンド $t = 1$**: $j_b = 2, k_b = 4$
  $k = 4$ から始まり、次のラウンドで $k$ が $+2$ シフト

- …$m = 5$ 回のラウンドで $k = 2, 4, 1, 3, 0$ と $2$ 刻みで全値を網羅（$\gcd(2,5)=1$ から）

この直感が `mul2_bijective_odd` と `i0Expected_surjective` の形式証明に対応している。
