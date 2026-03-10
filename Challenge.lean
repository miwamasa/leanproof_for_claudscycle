/-
  Challenge: Claude's Cycles — Decomposition Theorem
  ===================================================
  For use with https://github.com/leanprover/comparator

  Prove that for every odd m ≥ 3, the Cayley digraph on m³ vertices
  can be decomposed into exactly three directed Hamiltonian cycles.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-! ## Definitions -/

abbrev Vertex (m : ℕ) := Fin m × Fin m × Fin m

inductive Dir where
  | bumpi : Dir
  | bumpj : Dir
  | bumpk : Dir
  deriving DecidableEq, Repr, Fintype

/-- The "fiber index" s = (i + j + k) in Fin m. -/
def fiberIndex (m : ℕ) [NeZero m] (v : Vertex m) : Fin m :=
  v.1 + v.2.1 + v.2.2

def bump (m : ℕ) [NeZero m] (v : Vertex m) (d : Dir) : Vertex m :=
  match d with
  | Dir.bumpi => (v.1 + 1, v.2.1, v.2.2)
  | Dir.bumpj => (v.1, v.2.1 + 1, v.2.2)
  | Dir.bumpk => (v.1, v.2.1, v.2.2 + 1)

def dir0 (m : ℕ) [NeZero m] (v : Vertex m) : Dir :=
  let s := fiberIndex m v
  let i := v.1
  let j := v.2.1
  if s.val = 0 then
    if j.val = m - 1 then Dir.bumpi else Dir.bumpk
  else if s.val = m - 1 then
    if i.val > 0 then Dir.bumpj else Dir.bumpk
  else
    if i.val = m - 1 then Dir.bumpk else Dir.bumpj

def dir1 (m : ℕ) [NeZero m] (v : Vertex m) : Dir :=
  let s := fiberIndex m v
  let i := v.1
  if s.val = 0 then
    Dir.bumpj
  else if s.val = m - 1 then
    if i.val > 0 then Dir.bumpk else Dir.bumpj
  else
    Dir.bumpi

def dir2 (m : ℕ) [NeZero m] (v : Vertex m) : Dir :=
  let s := fiberIndex m v
  let i := v.1
  let j := v.2.1
  if s.val = 0 then
    if j.val < m - 1 then Dir.bumpi else Dir.bumpk
  else if s.val = m - 1 then
    Dir.bumpi
  else
    if i.val < m - 1 then Dir.bumpk else Dir.bumpj

def successor (m : ℕ) [NeZero m] (dirFn : Vertex m → Dir) (v : Vertex m) : Vertex m :=
  bump m v (dirFn v)

def orbit (m : ℕ) [NeZero m] (dirFn : Vertex m → Dir) (start : Vertex m) :
    (n : ℕ) → Vertex m
  | 0 => start
  | n + 1 => successor m dirFn (orbit m dirFn start n)

/-! ## Challenge: Prove this theorem -/

theorem claude_decomposition (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3) :
    (∃ start₀, orbit m (dir0 m) start₀ (m ^ 3) = start₀ ∧
      ∀ v, ∃ n : Fin (m ^ 3), orbit m (dir0 m) start₀ n.val = v) ∧
    (∃ start₁, orbit m (dir1 m) start₁ (m ^ 3) = start₁ ∧
      ∀ v, ∃ n : Fin (m ^ 3), orbit m (dir1 m) start₁ n.val = v) ∧
    (∃ start₂, orbit m (dir2 m) start₂ (m ^ 3) = start₂ ∧
      ∀ v, ∃ n : Fin (m ^ 3), orbit m (dir2 m) start₂ n.val = v) ∧
    (∀ v : Vertex m,
      ({dir0 m v, dir1 m v, dir2 m v} : Finset Dir) = {Dir.bumpi, Dir.bumpj, Dir.bumpk}) := by
  sorry
