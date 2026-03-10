# Lean 4 Proof Summary: Claude's Cycles

## Overview

**File:** `ClaudeCycles.lean` (3,389 lines, zero `sorry`)
**Lean version:** Lean 4 v4.29.0-rc2 with Mathlib
**Paper:** Don Knuth, "Claude's Cycles" (28 Feb 2026; revised 02 Mar 2026)

### Main Theorem

For every odd integer m >= 3, the Cayley digraph on m^3 vertices with three types of arcs
(bumping i, j, or k modulo m) can be decomposed into exactly three directed Hamiltonian cycles.

```lean
theorem claude_decomposition (m : N) [NeZero m]
    (hm_odd : m % 2 = 1) (hm_ge : m >= 3) :
    (exists start0, orbit m (dir0 m) start0 (m ^ 3) = start0 /\
      forall v, exists n : Fin (m ^ 3), orbit m (dir0 m) start0 n.val = v) /\
    (exists start1, orbit m (dir1 m) start1 (m ^ 3) = start1 /\
      forall v, exists n : Fin (m ^ 3), orbit m (dir1 m) start1 n.val = v) /\
    (exists start2, orbit m (dir2 m) start2 (m ^ 3) = start2 /\
      forall v, exists n : Fin (m ^ 3), orbit m (dir2 m) start2 n.val = v) /\
    (forall v : Vertex m,
      ({dir0 m v, dir1 m v, dir2 m v} : Finset Dir) = {Dir.bumpi, Dir.bumpj, Dir.bumpk})
```

---

## File Structure

### Section 1: Basic Definitions (lines 17--35)

| Definition | Type | Description |
|------------|------|-------------|
| `Vertex m` | `Fin m x Fin m x Fin m` | Vertices (i, j, k) of the Cayley digraph |
| `Dir` | `bumpi \| bumpj \| bumpk` | Three arc directions |
| `fiberIndex` | `Vertex m -> Fin m` | Fiber index s = (i + j + k) mod m |
| `bump` | `Vertex m -> Dir -> Vertex m` | Apply a direction to a vertex |

### Section 2: Direction Functions (lines 37--77)

Three direction functions that together form a permutation of `{bumpi, bumpj, bumpk}` at each vertex:

| Function | Decision logic |
|----------|---------------|
| `dir0` | Based on s, i, j: primary "zigzag" cycle |
| `dir1` | Based on s, i: secondary cycle |
| `dir2` | Based on s, i, j: tertiary cycle |

Supporting definitions:
- `successor`: Apply `bump` using a direction function
- `orbit`: Iterate `successor` n times from a starting vertex

### Section 3: Key Properties (lines 79--133)

- **`fiber_advances`**: Bumping any coordinate advances the fiber index by 1 mod m.
- **`directions_are_permutation`**: At every vertex, `{dir0, dir1, dir2} = {bumpi, bumpj, bumpk}`.
- **`bump_injective`**: Bump is injective in the vertex argument for each fixed direction.
- **`successor_dir0_injective`**: The successor map under `dir0` is injective.

### Section 4: Cycle 0 -- Block Analysis (lines 135--1730)

Cycle 0 is proved Hamiltonian by decomposing the m^3 vertices into m "blocks" of m^2 vertices each, indexed by the i-coordinate.

#### 4.1 The i = 0 Block (lines 268--801)

- **`i0Expected(t, r)`**: Closed-form formula for the orbit position at step `t*m + r` within the i=0 block.
- **`orbit_i0_explicit`**: The orbit matches `i0Expected` for all `t*m + r < m^2`.
- **`i0Expected_injective`**: Proved by extracting `r` from the fiber index, then `t` from the j+k coordinate using `gcd(2, m) = 1`.
- **`i0_block_complete`**: Every vertex with i=0 appears in the orbit.

#### 4.2 Block Transitions (lines 803--828)

- **`block_exit_bumps_i`**: At the end of each block, the direction is `bumpi`, transitioning to the next block.

#### 4.3 The i = m-1 Block (lines 829--1193)

Symmetric structure to the i=0 block with `lastExpected(t, r)`.

#### 4.4 Intermediate Blocks: 0 < i < m-1 (lines 1195--1547)

- **`midExpected(i, t, r)`**: Parametrized by the i-coordinate.
- Same orbit-matching and injectivity structure.

#### 4.5 Block Chaining (lines 1548--1730)

- **`orbit_reaches_block`**: After `i * m^2` steps, the orbit reaches block i.
- **`orbit_returns`**: After `m * m^2 = m^3` steps, the orbit returns to the start.

### Section 5: Cycle 0 Hamiltonicity (lines 1731--1787)

```lean
theorem cycle0_hamiltonian (m : N) [NeZero m]
    (hm_odd : m % 2 = 1) (hm_ge : m >= 3) :
    exists start : Vertex m,
      (orbit m (dir0 m) start (m ^ 3) = start) /\
      (forall v : Vertex m, exists n : Fin (m ^ 3),
        orbit m (dir0 m) start n.val = v)
```

Proved by combining block completeness with block chaining.

### Section 6: Cycles 1 and 2 (lines 1788--3348)

Cycles 1 and 2 follow a different but uniform proof architecture based on "super-rounds."

#### Common Architecture

Each cycle partitions the m^3 orbit steps into m **super-rounds** of m^2 steps each, indexed by a parameter u in Fin m. Within super-round u:
- Steps are indexed as `t * m + r` for `t, r in Fin m`.
- A closed-form **Expected function** maps `(u, t, r)` to the vertex at that orbit position.

The Hamiltonicity proof has four components:

| Component | Purpose |
|-----------|---------|
| `orbit_explicit` | The orbit matches `Expected(u, t, r)` at step `u*m^2 + t*m + r` |
| `Expected_injective` | Distinct `(u, t, r)` triples produce distinct vertices |
| `Expected_surjective` | Follows from injectivity on a finite type |
| `orbit_returns` | The orbit returns to start after m^3 steps |

#### Cycle 1 (lines 1898--2476)

- **`dir1Expected(u, t, r)`**: 2-branch formula (r=0 vs r>=1).
- **`dir1Expected_injective`**: Recovery strategy: r from fiber index, t from j+k using coprimality of 2 and m, u from j - t.

#### Cycle 2 (lines 2477--3348)

- **`dir2Expected(u, t, r)`**: 5-branch formula depending on whether the super-round is "non-special" (`j_u = ((m-2)*u) mod m < m-1`) or "special" (`j_u = m-1`).
- **`dir2Expected_injective`** (220 lines): The most complex proof in the formalization.
  - Recovery: r from fiber, then case analysis on special/non-special status of u1 and u2 (4 main cases x multiple sub-cases).
  - Key helper: `u_eq_of_m2_u_mod` reduces `(m-2)*u1 = (m-2)*u2 (mod m)` to `2*u1 = 2*u2 (mod m)` using `(m-2)*u + 2*u = m*u`.
  - `t_eq_of_two_t_mod` handles `2*t1 = 2*t2 (mod m)` by coprimality (m odd).

### Section 7: The Decomposition Theorem (lines 3350--3369)

Assembles all three Hamiltonian cycle theorems plus the direction permutation property.

### Section 8: Generalizability Stub (lines 3371--3389)

A placeholder for future work on generalizing the direction-classification scheme.

---

## Key Mathematical Techniques

### Coprimality of 2 and m (m odd)

The fundamental algebraic fact: `gcd(2, m) = 1` when m is odd. This is used to cancel factors of 2 in modular equations.

**`t_eq_of_two_t_mod`**: If `2*t1 = 2*t2 (mod m)` with m odd and `t1, t2 < m`, then `t1 = t2`.
Proof by contradiction: `m | 2*(t2-t1)` with `0 < 2*(t2-t1) < 2m` forces `2*(t2-t1) = m`, contradicting m odd.

**`u_eq_of_m2_u_mod`**: If `(m-2)*u1 = (m-2)*u2 (mod m)`, then `u1 = u2`.
Reduces to the above via `(m-2)*u + 2*u = m*u`, so `(m-2)*u = -2*u (mod m)`.

### Fiber Index for Parameter Recovery

The fiber index `s = (i + j + k) mod m` is invariant under all direction functions modulo the step count. This allows recovering the `r` parameter (intra-round step) from any vertex.

### Injectivity on Finite Types implies Surjectivity

```lean
private theorem dir1Expected_surjective ... :=
  Finite.surjective_of_injective (dir1Expected_injective m hm_odd hm_ge)
```

Since `Fin m x Fin m x Fin m` is finite, any injective function from it to itself is automatically surjective.

---

## Statistics

| Metric | Value |
|--------|-------|
| Total lines | 3,389 |
| Theorems/lemmas | ~110 |
| Definitions | ~20 |
| `sorry` count | 0 |
| Mathlib imports | 5 |
| Build time | ~100s |

### Lines by section

| Section | Lines | % |
|---------|-------|---|
| 1. Basic definitions | 60 | 2% |
| 2. Direction functions | 40 | 1% |
| 3. Key properties | 55 | 2% |
| 4. Cycle 0 (block analysis) | 1,595 | 47% |
| 5. Cycle 0 Hamiltonicity | 55 | 2% |
| 6. Cycles 1 and 2 | 1,560 | 46% |
| 7. Decomposition theorem | 20 | <1% |
| 8. Generalizability stub | 15 | <1% |

### Proof complexity

| Proof | Lines | Case splits |
|-------|-------|-------------|
| `dir2Expected_injective` | 220 | 25 (4 main x sub-cases) |
| `dir1Expected_injective` | 105 | 9 (3x3 on r1=0/r2=0) |
| `i0Expected_jk_injective` | 77 | 9 |
| `orbit_i0_explicit` | 65 | Induction on m^2 |
| `dir2_succ_mid` | 110 | 12 (fiber x coordinate cases) |
