# Claude's Cycles — Lean 4 Formal Proof

A complete formal verification in Lean 4 of the main theorem from Don Knuth's paper
**"Claude's Cycles"** (28 Feb 2026; revised 02 Mar 2026).

## Theorem

For every odd integer $m \geq 3$, the Cayley digraph on $m^3$ vertices
$ijk$ ($0 \leq i,j,k < m$) with arcs
$ijk \to (i{+}1)jk$, $i(j{+}1)k$, $ij(k{+}1)$ (all mod $m$)
can be decomposed into exactly **three directed Hamiltonian cycles**.

```lean
theorem claude_decomposition (m : ℕ) [NeZero m]
    (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3) :
    -- Cycle 0 is Hamiltonian
    (∃ start₀, orbit m (dir0 m) start₀ (m ^ 3) = start₀ ∧
      ∀ v, ∃ n : Fin (m ^ 3), orbit m (dir0 m) start₀ n.val = v) ∧
    -- Cycle 1 is Hamiltonian
    (∃ start₁, orbit m (dir1 m) start₁ (m ^ 3) = start₁ ∧
      ∀ v, ∃ n : Fin (m ^ 3), orbit m (dir1 m) start₁ n.val = v) ∧
    -- Cycle 2 is Hamiltonian
    (∃ start₂, orbit m (dir2 m) start₂ (m ^ 3) = start₂ ∧
      ∀ v, ∃ n : Fin (m ^ 3), orbit m (dir2 m) start₂ n.val = v) ∧
    -- The three directions form a permutation at every vertex
    (∀ v : Vertex m,
      ({dir0 m v, dir1 m v, dir2 m v} : Finset Dir) =
        {Dir.bumpi, Dir.bumpj, Dir.bumpk})
```

## Status

- **3,389 lines**, **zero `sorry`** — fully machine-checked
- Lean 4 v4.29.0-rc2 with Mathlib v4.29.0-rc2
- Build time: ~100 seconds

## Quick Start

### Prerequisites

Install [elan](https://github.com/leanprover/elan) (the Lean version manager).

### Build

```bash
lake build
```

This will download Mathlib, compile all dependencies, and type-check the proof.
A successful build with no errors confirms the theorem is correct.

### Verify with Comparator

This project includes a [Comparator](https://github.com/leanprover/comparator)-compatible challenge:

```bash
comparator --config config.json
```

- `Challenge.lean` — theorem statement with `sorry`
- `ClaudeCycles.lean` — the complete proof (solution)
- `config.json` — Comparator configuration

## File Structure

```
.
├── ClaudeCycles.lean        # Main proof (3,389 lines, zero sorry)
├── Challenge.lean           # Comparator challenge (theorem with sorry)
├── config.json              # Comparator configuration
├── Lemmas.lean              # Auxiliary lemmas (early development)
├── lakefile.toml            # Lake build configuration
├── lean-toolchain           # Lean version pin (v4.29.0-rc2)
├── lake-manifest.json       # Dependency lock file
└── doc/
    ├── lean_proof_summary.md                    # Proof structure overview
    └── lean_proof_of_knuth_claudecycle_paper.tex # LaTeX paper with Lean snippets
```

## Proof Architecture

The proof decomposes into three independent Hamiltonicity arguments:

### Cycle 0 — Block Analysis (47% of proof)

The $m^3$ vertices are partitioned into $m$ "blocks" by the $i$-coordinate.
Each block of $m^2$ vertices is traversed via a closed-form orbit formula,
then blocks are chained together via `bumpi` transitions.

- **i = 0 block**: Formula `i0Expected(t, r)` with injectivity via fiber index recovery and coprimality of 2 and $m$.
- **i = m−1 block**: Symmetric structure with `lastExpected(t, r)`.
- **Intermediate blocks**: Parametrized by `midExpected(i, t, r)`.

### Cycles 1 and 2 — Super-Round Architecture (46% of proof)

Both cycles use a uniform framework of $m$ "super-rounds" of $m^2$ steps each:

| Component | Purpose |
|-----------|---------|
| `Expected(u, t, r)` | Closed-form vertex at step $u \cdot m^2 + t \cdot m + r$ |
| `orbit_explicit` | Orbit matches the Expected formula |
| `Expected_injective` | Distinct $(u,t,r)$ triples → distinct vertices |
| `orbit_returns` | Orbit returns to start after $m^3$ steps |

**Cycle 2** has the most complex injectivity proof (220 lines, 25 case splits)
due to its 5-branch Expected formula with "special" vs "non-special" super-rounds.

### Key Mathematical Techniques

- **Coprimality**: $\gcd(2, m) = 1$ for odd $m$ enables cancellation in modular equations.
- **Fiber index**: $s = (i + j + k) \bmod m$ recovers the intra-round step parameter.
- **Finite injectivity → surjectivity**: `Finite.surjective_of_injective` from Mathlib.

## Proof Statistics

| Metric | Value |
|--------|-------|
| Total lines | 3,389 |
| Theorems/lemmas | ~110 |
| `sorry` count | **0** |
| Build time | ~100s |

| Most complex proofs | Lines | Case splits |
|---------------------|-------|-------------|
| `dir2Expected_injective` | 220 | 25 |
| `dir1Expected_injective` | 105 | 9 |
| `i0Expected_jk_injective` | 77 | 9 |

## References

- Don Knuth, "Claude's Cycles" (28 Feb 2026; revised 02 Mar 2026)
- [Lean 4](https://lean-lang.org/)
- [Mathlib](https://github.com/leanprover-community/mathlib4)

## License

MIT License. See [LICENSE](LICENSE).
