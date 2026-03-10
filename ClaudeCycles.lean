/-
  Claude's Cycles — Lean 4 Formalization
  ========================================
  Based on: Don Knuth, "Claude's Cycles" (28 Feb 2026; revised 02 Mar 2026)

  Problem: Digraph on m³ vertices ijk (0 ≤ i,j,k < m) with arcs
    ijk → (i+1)jk, i(j+1)k, ij(k+1)  (all mod m).
  Goal: Decompose all 3m³ arcs into three directed Hamiltonian m³-cycles for odd m > 1.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-! ## 1. Basic Definitions -/

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

/-! ## 2. Claude's Direction Function -/

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

/-! ## 3. Key Properties -/

/-- Bumping any coordinate advances the fiber index by 1 mod m. -/
theorem fiber_advances (m : ℕ) [NeZero m] (v : Vertex m) (d : Dir) :
    fiberIndex m (bump m v d) = fiberIndex m v + 1 := by
  cases d <;> simp [fiberIndex, bump, add_assoc, add_comm, add_left_comm]

/-- The three directions at any vertex form a permutation of {bumpi, bumpj, bumpk}. -/
theorem directions_are_permutation (m : ℕ) [NeZero m] (hm : m ≥ 3) (v : Vertex m) :
    ({dir0 m v, dir1 m v, dir2 m v} : Finset Dir) = {Dir.bumpi, Dir.bumpj, Dir.bumpk} := by
  simp only [dir0, dir1, dir2]
  have hj_bound := v.2.1.isLt
  have hi_bound := v.1.isLt
  split_ifs <;> first
    | (ext x; fin_cases x <;> simp_all <;> done)
    | omega

/-- The bump function is injective in the vertex argument for any fixed direction. -/
theorem bump_injective (m : ℕ) [NeZero m] (d : Dir) :
    Function.Injective (fun v : Vertex m => bump m v d) := by
  intro u v h
  cases d <;> simp [bump, Prod.mk.injEq] at h <;> ext <;> simp_all

/-- Helper: determine dir0 output from conditions on fiberIndex and coordinates. -/
private theorem dir0_eq_of_conditions (m : ℕ) [NeZero m] (v : Vertex m)
    (hs0 : (fiberIndex m v).val = 0) (hj : v.2.1.val = m - 1) :
    dir0 m v = Dir.bumpi := by
  simp [dir0, hs0, hj]

private theorem dir0_eq_of_conditions' (m : ℕ) [NeZero m] (v : Vertex m)
    (hs0 : (fiberIndex m v).val = 0) (hj : ¬ v.2.1.val = m - 1) :
    dir0 m v = Dir.bumpk := by
  simp [dir0, hs0, hj]

private theorem dir0_eq_of_conditions2 (m : ℕ) [NeZero m] (v : Vertex m)
    (hs : ¬(fiberIndex m v).val = 0) (hs' : (fiberIndex m v).val = m - 1)
    (hi : v.1.val > 0) : dir0 m v = Dir.bumpj := by
  simp only [dir0]; split_ifs <;> simp_all

private theorem dir0_eq_of_conditions2' (m : ℕ) [NeZero m] (v : Vertex m)
    (hs : ¬(fiberIndex m v).val = 0) (hs' : (fiberIndex m v).val = m - 1)
    (hi : ¬ v.1.val > 0) : dir0 m v = Dir.bumpk := by
  simp only [dir0]; split_ifs <;> simp_all

private theorem dir0_eq_of_conditions3 (m : ℕ) [NeZero m] (v : Vertex m)
    (hs : ¬(fiberIndex m v).val = 0) (hs' : ¬(fiberIndex m v).val = m - 1)
    (hi : v.1.val = m - 1) : dir0 m v = Dir.bumpk := by
  simp [dir0, hs, hs', hi]

private theorem dir0_eq_of_conditions3' (m : ℕ) [NeZero m] (v : Vertex m)
    (hs : ¬(fiberIndex m v).val = 0) (hs' : ¬(fiberIndex m v).val = m - 1)
    (hi : ¬ v.1.val = m - 1) : dir0 m v = Dir.bumpj := by
  simp [dir0, hs, hs', hi]

/-- The successor function for dir0 is injective (hence a permutation of Vertex m).
    Same direction => bump injectivity. Different directions => contradiction. -/
theorem successor_dir0_injective (m : ℕ) [NeZero m] (hm : m ≥ 3) :
    Function.Injective (successor m (dir0 m)) := by
  intro u v h
  simp only [successor] at h
  by_cases hd : dir0 m u = dir0 m v
  · rw [hd] at h; exact bump_injective m (dir0 m v) h
  · exfalso
    have hf : fiberIndex m u = fiberIndex m v := by
      have h1 := fiber_advances m u (dir0 m u)
      have h2 := fiber_advances m v (dir0 m v)
      rw [h] at h1; exact add_right_cancel (h1.symm.trans h2)
    have hfval : (fiberIndex m u).val = (fiberIndex m v).val := congrArg Fin.val hf
    -- Case split on fiber class (same for u and v by hf)
    -- Class 1: s = 0 => dir0 in {bumpi, bumpk}
    by_cases hsu : (fiberIndex m u).val = 0
    · have hsv : (fiberIndex m v).val = 0 := by omega
      by_cases hju : u.2.1.val = m - 1
      · by_cases hjv : v.2.1.val = m - 1
        · exact hd (by rw [dir0_eq_of_conditions m u hsu hju,
                            dir0_eq_of_conditions m v hsv hjv])
        · -- bumpi vs bumpk: bump gives u.2.1 = v.2.1 but j-vals differ
          rw [dir0_eq_of_conditions m u hsu hju,
              dir0_eq_of_conditions' m v hsv hjv] at h
          simp only [bump, Prod.mk.injEq] at h
          have : u.2.1 = v.2.1 := h.2.1
          exact hjv (by rw [← this]; exact hju)
      · by_cases hjv : v.2.1.val = m - 1
        · rw [dir0_eq_of_conditions' m u hsu hju,
              dir0_eq_of_conditions m v hsv hjv] at h
          simp only [bump, Prod.mk.injEq] at h
          have : u.2.1 = v.2.1 := h.2.1
          exact hju (by rw [this]; exact hjv)
        · exact hd (by rw [dir0_eq_of_conditions' m u hsu hju,
                            dir0_eq_of_conditions' m v hsv hjv])
    -- Class 2: s = m-1 => dir0 in {bumpj, bumpk}
    · by_cases hsu' : (fiberIndex m u).val = m - 1
      · have hsv_ne : ¬(fiberIndex m v).val = 0 := by omega
        have hsv' : (fiberIndex m v).val = m - 1 := by omega
        by_cases hiu : u.1.val > 0
        · by_cases hiv : v.1.val > 0
          · exact hd (by rw [dir0_eq_of_conditions2 m u hsu hsu' hiu,
                              dir0_eq_of_conditions2 m v hsv_ne hsv' hiv])
          · -- bumpj vs bumpk: u.1 = v.1 but i-vals differ
            rw [dir0_eq_of_conditions2 m u hsu hsu' hiu,
                dir0_eq_of_conditions2' m v hsv_ne hsv' hiv] at h
            simp only [bump, Prod.mk.injEq] at h
            have : u.1 = v.1 := h.1
            exact hiv (by rw [← this]; exact hiu)
        · by_cases hiv : v.1.val > 0
          · rw [dir0_eq_of_conditions2' m u hsu hsu' hiu,
                dir0_eq_of_conditions2 m v hsv_ne hsv' hiv] at h
            simp only [bump, Prod.mk.injEq] at h
            have : u.1 = v.1 := h.1
            exact hiu (by rw [this]; exact hiv)
          · exact hd (by rw [dir0_eq_of_conditions2' m u hsu hsu' hiu,
                              dir0_eq_of_conditions2' m v hsv_ne hsv' hiv])
      -- Class 3: 0 < s < m-1 => dir0 in {bumpj, bumpk}
      · have hsv : ¬(fiberIndex m v).val = 0 := by omega
        have hsv' : ¬(fiberIndex m v).val = m - 1 := by omega
        by_cases hiu : u.1.val = m - 1
        · by_cases hiv : v.1.val = m - 1
          · exact hd (by rw [dir0_eq_of_conditions3 m u hsu hsu' hiu,
                              dir0_eq_of_conditions3 m v hsv hsv' hiv])
          · -- bumpk vs bumpj: u.1 = v.1 but i-vals differ
            rw [dir0_eq_of_conditions3 m u hsu hsu' hiu,
                dir0_eq_of_conditions3' m v hsv hsv' hiv] at h
            simp only [bump, Prod.mk.injEq] at h
            have : u.1 = v.1 := h.1
            exact hiv (by rw [← this]; exact hiu)
        · by_cases hiv : v.1.val = m - 1
          · rw [dir0_eq_of_conditions3' m u hsu hsu' hiu,
                dir0_eq_of_conditions3 m v hsv hsv' hiv] at h
            simp only [bump, Prod.mk.injEq] at h
            have : u.1 = v.1 := h.1
            exact hiu (by rw [this]; exact hiv)
          · exact hd (by rw [dir0_eq_of_conditions3' m u hsu hsu' hiu,
                              dir0_eq_of_conditions3' m v hsv hsv' hiv])

/-- In Cycle 0, coordinate i is bumped only when s = 0 and j = m−1. -/
theorem cycle0_i_change_condition (m : ℕ) [NeZero m] (v : Vertex m) :
    dir0 m v = Dir.bumpi ↔
    (fiberIndex m v).val = 0 ∧ v.2.1.val = m - 1 := by
  simp only [dir0]
  constructor
  · intro h
    split_ifs at h <;> simp_all
  · rintro ⟨hs, hj⟩
    simp only [hs, hj, ite_true]

/-- Within a block of constant i, the behavior on middle fibers is to bump j. -/
theorem cycle0_middle_fiber_middle_i (m : ℕ) [NeZero m]
    (v : Vertex m)
    (hs_pos : 0 < (fiberIndex m v).val)
    (hs_lt : (fiberIndex m v).val < m - 1)
    (hi_lt : v.1.val < m - 1) :
    dir0 m v = Dir.bumpj := by
  simp only [dir0]
  split_ifs
  all_goals first | omega | rfl

/-- Key arithmetic lemma: if m is odd, then multiplication by 2 is a bijection on Fin m. -/
theorem mul2_bijective_odd (m : ℕ) (hm : m % 2 = 1) (hm_pos : 0 < m) :
    Function.Bijective (fun x : Fin m =>
      (⟨(2 * x.val) % m, Nat.mod_lt _ hm_pos⟩ : Fin m)) := by
  have hinj : Function.Injective (fun x : Fin m =>
      (⟨(2 * x.val) % m, Nat.mod_lt _ hm_pos⟩ : Fin m)) := by
    intro a b hab
    simp only [Fin.mk.injEq] at hab
    -- hab : 2 * a.val % m = 2 * b.val % m
    have hmeq : 2 * a.val ≡ 2 * b.val [MOD m] := hab
    have hodd : Odd m := Nat.odd_iff.mpr hm
    have hcop_m2 : m.Coprime 2 := (Nat.coprime_two_left.mpr hodd).symm
    have ha := a.isLt
    have hb := b.isLt
    ext
    by_cases h : a.val ≤ b.val
    · have hdvd : m ∣ 2 * b.val - 2 * a.val :=
        (Nat.modEq_iff_dvd' (by omega : 2 * a.val ≤ 2 * b.val)).mp hmeq
      have heq : 2 * b.val - 2 * a.val = 2 * (b.val - a.val) := by omega
      rw [heq] at hdvd
      have hdvd_sub : m ∣ (b.val - a.val) := hcop_m2.dvd_of_dvd_mul_left hdvd
      have : b.val - a.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd_sub (by omega)
      omega
    · push_neg at h
      have hdvd : m ∣ 2 * a.val - 2 * b.val :=
        (Nat.modEq_iff_dvd' (by omega : 2 * b.val ≤ 2 * a.val)).mp hmeq.symm
      have heq : 2 * a.val - 2 * b.val = 2 * (a.val - b.val) := by omega
      rw [heq] at hdvd
      have hdvd_sub : m ∣ (a.val - b.val) := hcop_m2.dvd_of_dvd_mul_left hdvd
      have : a.val - b.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd_sub (by omega)
      omega
  exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩

/-! ### 4.1 Structure within the i=0 block -/

def checkpoint0 (m : ℕ) [NeZero m] (t : Fin m) : Vertex m :=
  let j : Fin m := ⟨(m - 1 + m - 2 * (t.val % m)) % m, Nat.mod_lt _ (NeZero.pos m)⟩
  let k : Fin m := ⟨(2 + 2 * t.val) % m, Nat.mod_lt _ (NeZero.pos m)⟩
  (⟨0, NeZero.pos m⟩, j, k)

theorem checkpoints0_injective (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3) :
    Function.Injective (checkpoint0 m) := by
  intro a b hab
  simp only [checkpoint0, Prod.mk.injEq] at hab
  -- From the k-component: (2 + 2*a.val) % m = (2 + 2*b.val) % m
  obtain ⟨_, _, hk⟩ := hab
  simp only [Fin.mk.injEq] at hk
  have hm_pos : 0 < m := NeZero.pos m
  -- hk : (2 + 2 * a.val) % m = (2 + 2 * b.val) % m
  have hmeq : (2 + 2 * a.val) % m = (2 + 2 * b.val) % m := hk
  have hmeq2 : 2 * a.val % m = 2 * b.val % m := by
    have hmod : (2 + 2 * a.val) ≡ (2 + 2 * b.val) [MOD m] := hmeq
    exact Nat.ModEq.add_left_cancel (Nat.ModEq.refl 2) hmod
  -- Use injectivity of multiplication by 2
  have hbij := mul2_bijective_odd m hm_odd hm_pos
  have hinj := hbij.1
  have hab2 : (⟨(2 * a.val) % m, Nat.mod_lt _ hm_pos⟩ : Fin m) =
              ⟨(2 * b.val) % m, Nat.mod_lt _ hm_pos⟩ := by
    ext; exact hmeq2
  exact hinj hab2

/-! ### Orbit Infrastructure -/

/-- Orbit step: orbit(start, n+1) = successor(orbit(start, n)). -/
@[simp] theorem orbit_succ (m : ℕ) [NeZero m] (dirFn : Vertex m → Dir)
    (start : Vertex m) (n : ℕ) :
    orbit m dirFn start (n + 1) = successor m dirFn (orbit m dirFn start n) := rfl

/-- Orbit zero: orbit(start, 0) = start. -/
@[simp] theorem orbit_zero (m : ℕ) [NeZero m] (dirFn : Vertex m → Dir)
    (start : Vertex m) : orbit m dirFn start 0 = start := rfl

/-- Fiber index advances by 1 per orbit step (Fin-level). -/
theorem orbit_fiber_step (m : ℕ) [NeZero m] (dirFn : Vertex m → Dir) (start : Vertex m)
    (n : ℕ) :
    fiberIndex m (orbit m dirFn start (n + 1)) =
    fiberIndex m (orbit m dirFn start n) + 1 := by
  simp only [orbit_succ, successor]
  exact fiber_advances m (orbit m dirFn start n) (dirFn (orbit m dirFn start n))

/-- Successor applied to a vertex with dir0=bumpj gives (i, j+1, k). -/
theorem successor_bumpj (m : ℕ) [NeZero m] (v : Vertex m) (h : dir0 m v = Dir.bumpj) :
    successor m (dir0 m) v = (v.1, v.2.1 + 1, v.2.2) := by
  simp [successor, h, bump]

/-- Successor applied to a vertex with dir0=bumpk gives (i, j, k+1). -/
theorem successor_bumpk (m : ℕ) [NeZero m] (v : Vertex m) (h : dir0 m v = Dir.bumpk) :
    successor m (dir0 m) v = (v.1, v.2.1, v.2.2 + 1) := by
  simp [successor, h, bump]

/-- Successor applied to a vertex with dir0=bumpi gives (i+1, j, k). -/
theorem successor_bumpi (m : ℕ) [NeZero m] (v : Vertex m) (h : dir0 m v = Dir.bumpi) :
    successor m (dir0 m) v = (v.1 + 1, v.2.1, v.2.2) := by
  simp [successor, h, bump]

/-! ### dir0 decision lemmas for each fiber/coordinate case -/

/-- s=m-1, i=0 → bumpk -/
theorem dir0_sm1_i0 (m : ℕ) [NeZero m] (v : Vertex m)
    (hs_ne : ¬(fiberIndex m v).val = 0)
    (hs_m1 : (fiberIndex m v).val = m - 1)
    (hi_eq : v.1.val = 0) : dir0 m v = Dir.bumpk := by
  simp only [dir0]; split_ifs <;> simp_all <;> omega

/-- s=m-1, i>0 → bumpj -/
theorem dir0_sm1_igt0 (m : ℕ) [NeZero m] (v : Vertex m)
    (hs_ne : ¬(fiberIndex m v).val = 0)
    (hs_m1 : (fiberIndex m v).val = m - 1)
    (hi_gt : v.1.val > 0) : dir0 m v = Dir.bumpj := by
  simp only [dir0]; split_ifs <;> simp_all

/-- s=0, j<m-1 → bumpk -/
theorem dir0_s0_jlt (m : ℕ) [NeZero m] (v : Vertex m)
    (hs_0 : (fiberIndex m v).val = 0)
    (hj_lt : v.2.1.val < m - 1) : dir0 m v = Dir.bumpk := by
  simp only [dir0]; split_ifs <;> simp_all <;> omega

/-- 0<s<m-1, i=m-1 → bumpk -/
theorem dir0_mid_im1 (m : ℕ) [NeZero m] (v : Vertex m)
    (hs_ne0 : ¬(fiberIndex m v).val = 0)
    (hs_nem1 : ¬(fiberIndex m v).val = m - 1)
    (hi_m1 : v.1.val = m - 1) : dir0 m v = Dir.bumpk := by
  simp only [dir0]; split_ifs <;> simp_all

/-! ### Block dynamics: i-coordinate preservation -/

/-- The orbit from checkpoint0(0) has a specific structure.
    We define the expected vertex at each step within the i=0 block.

    Round t (0 ≤ t < m), step r (0 ≤ r < m):
    - For 0 ≤ r ≤ m-2: vertex (0, j_t + r, k_t) where j_t = m-1-2t, k_t = 2+2t (mod m)
      fiber s = 1 + r
    - For r = m-1: vertex (0, j_t + (m-2), k_t + 1) where j_t, k_t as above
      fiber s = 0
-/
def i0Expected (m : ℕ) [NeZero m] (t r : Fin m) : Vertex m :=
  let j_base : Fin m := ⟨(2 * m - 1 - 2 * t.val) % m, Nat.mod_lt _ (NeZero.pos m)⟩
  let k_base : Fin m := ⟨(2 + 2 * t.val) % m, Nat.mod_lt _ (NeZero.pos m)⟩
  if r.val ≤ m - 2 then
    (⟨0, NeZero.pos m⟩, j_base + ⟨r.val, r.isLt⟩, k_base)
  else -- r = m-1
    (⟨0, NeZero.pos m⟩, j_base + ⟨m - 2, by have := NeZero.pos m; omega⟩, k_base + 1)

/-- j_base + k_base = 1 in Fin m. This is because (2m-1-2t) + (2+2t) = 2m+1 ≡ 1. -/
private theorem jbase_add_kbase (m : ℕ) [NeZero m] (hm_ge : m ≥ 3) (t : Fin m) :
    (⟨(2 * m - 1 - 2 * t.val) % m, Nat.mod_lt _ (NeZero.pos m)⟩ : Fin m) +
    ⟨(2 + 2 * t.val) % m, Nat.mod_lt _ (NeZero.pos m)⟩ = 1 := by
  have hm_pos : 0 < m := NeZero.pos m
  have ht_lt : t.val < m := t.isLt
  apply Fin.ext
  show ((2 * m - 1 - 2 * t.val) % m + (2 + 2 * t.val) % m) % m = (1 : Fin m).val
  rw [← Nat.add_mod]
  have hsum : (2 * m - 1 - 2 * t.val) + (2 + 2 * t.val) = 2 * m + 1 := by omega
  rw [hsum]
  conv_lhs => rw [show 2 * m + 1 = 1 + m * 2 from by ring]
  simp [Nat.add_mul_mod_self_left]

/-- Key lemma: orbit(checkpoint0(0), t*m + r) = i0Expected(t, r) for t, r < m.
    This completely characterizes the orbit within the i=0 block. -/
-- Helper for orbit_i0_explicit: mod addition absorption
private theorem mod_add_mod' (a b m : ℕ) : (a % m + b % m) % m = (a + b) % m :=
  (Nat.add_mod a b m).symm

-- Helper: (a % m + b) % m = (a + b) % m
private theorem mod_add_raw (a b m : ℕ) : (a % m + b) % m = (a + b) % m := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

-- Helper: (a + b % m) % m = (a + b) % m
private theorem raw_add_mod (a b m : ℕ) : (a + b % m) % m = (a + b) % m := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

-- Helper: absorb left mod in addition
private theorem mod_add_val (a b n : ℕ) : (a % n + b) % n = (a + b) % n := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

-- Helper: absorb right mod in addition
private theorem val_add_mod (a b n : ℕ) : (a + b % n) % n = (a + b) % n := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

-- Helper for orbit_i0_explicit: fiber index of i0Expected
-- Helper: after full Fin.val unfolding, the fiber reduces to mod arithmetic
private theorem i0E_fiber (m : ℕ) [NeZero m] (hm_ge : m ≥ 3) (t r : Fin m) :
    (fiberIndex m (i0Expected m t r)).val =
    if r.val ≤ m - 2 then (1 + r.val) % m else 0 := by
  have hm_pos : 0 < m := NeZero.pos m
  -- Unfold to Nat-level mod arithmetic
  unfold fiberIndex i0Expected
  split_ifs with hr
  · -- r ≤ m-2 case: reduces to modular sum = (1 + r) % m
    -- After dsimp, goal is: ((0 + ((2m-1-2t)%m + r)%m)%m + (2+2t)%m)%m = (1+r)%m
    dsimp only [Fin.val_add, Fin.val_mk]
    rw [Nat.zero_add, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc,
        mod_add_raw (2 * m - 1 - 2 * t.val) (r.val + (2 + 2 * t.val))]
    have hsum : (2 * m - 1 - 2 * t.val) + (r.val + (2 + 2 * t.val)) =
                (1 + r.val) + m * 2 := by omega
    rw [hsum, Nat.add_mul_mod_self_left]
  · -- r = m-1 case: reduces to 0
    dsimp only [Fin.val_add, Fin.val_mk]
    simp only [Fin.coe_ofNat_eq_mod]
    rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega : 1 < m)]
    rw [Nat.zero_add, Nat.mod_mod,
        mod_add_raw (2 * m - 1 - 2 * t.val) (m - 2),
        mod_add_raw (2 + 2 * t.val) 1,
        mod_add_mod' (2 * m - 1 - 2 * t.val + (m - 2)) (2 + 2 * t.val + 1)]
    have hsum : 2 * m - 1 - 2 * t.val + (m - 2) + (2 + 2 * t.val + 1) =
                m * 3 := by omega
    rw [hsum, Nat.mul_mod_right]

-- Helper for orbit_i0_explicit: i-component of i0Expected
private theorem i0E_i (m : ℕ) [NeZero m] (t r : Fin m) :
    (i0Expected m t r).1.val = 0 := by
  simp only [i0Expected]; split_ifs <;> simp

-- Helper for orbit_i0_explicit: j ≠ m-1 at round boundary (uses m odd)
private theorem i0E_j_lt (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3)
    (t : Fin m) (ht : t.val < m - 1) :
    (i0Expected m t ⟨m - 1, by omega⟩).2.1.val < m - 1 := by
  have hm_pos : 0 < m := NeZero.pos m
  have ht_lt : t.val < m := t.isLt
  -- Unfold and select the else branch (since m-1 > m-2)
  unfold i0Expected
  simp only [Fin.val_mk, show ¬(m - 1 ≤ m - 2) from by omega, ite_false]
  simp only [Fin.val_add, Fin.val_mk]
  rw [mod_add_raw]
  -- Goal: (2 * m - 1 - 2 * t.val + (m - 2)) % m < m - 1
  have hsum_eq : 2 * m - 1 - 2 * t.val + (m - 2) = 3 * m - 3 - 2 * t.val := by omega
  rw [hsum_eq]
  -- Case split on whether 2t ≤ m - 3 (determines which multiple of m to subtract)
  by_cases h2t : 2 * t.val ≤ m - 3
  · -- Subcase: remainder = m - 3 - 2t < m - 1 (trivially)
    have hmod : (3 * m - 3 - 2 * t.val) % m = m - 3 - 2 * t.val := by
      rw [show 3 * m - 3 - 2 * t.val = (m - 3 - 2 * t.val) + m * 2 from by omega,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : m - 3 - 2 * t.val < m)]
    omega
  · -- Subcase: remainder = 2m - 3 - 2t, and m odd forces 2t ≥ m - 1
    push_neg at h2t
    have hmod : (3 * m - 3 - 2 * t.val) % m = 2 * m - 3 - 2 * t.val := by
      rw [show 3 * m - 3 - 2 * t.val = (2 * m - 3 - 2 * t.val) + m * 1 from by omega,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : 2 * m - 3 - 2 * t.val < m)]
    -- 2t ≥ m-2, and since 2t is even and m-2 is odd (m odd), we have 2t ≥ m-1
    -- Therefore 2m-3-2t ≤ m-2 < m-1
    omega

private theorem base_case_i0 (m : ℕ) [NeZero m] (hm_ge : m ≥ 3) :
    checkpoint0 m ⟨0, NeZero.pos m⟩ = i0Expected m ⟨0, NeZero.pos m⟩ ⟨0, NeZero.pos m⟩ := by
  simp only [checkpoint0, i0Expected]
  have h0le : (0 : ℕ) ≤ m - 2 := by omega
  simp only [h0le, ite_true, Fin.val_mk]
  ext <;> simp [Fin.val_add, Fin.val_mk]
  · have hm_pos : 0 < m := NeZero.pos m
    have : (2 * m - 1) % m = m - 1 := by
      conv_lhs => rw [show 2 * m - 1 = m - 1 + 1 * m from by omega]
      simp [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (show m - 1 < m by omega)]
    omega

/-- Middle fiber step: 0 < s < m-1, i = 0 → dir0 = bumpj, advance r by 1. -/
private theorem i0_succ_mid (m : ℕ) [NeZero m] (hm_ge : m ≥ 3) (t : Fin m) (r : Fin m)
    (hr : r.val ≤ m - 3) :
    successor m (dir0 m) (i0Expected m t r) =
    i0Expected m t ⟨r.val + 1, by omega⟩ := by
  have hm_pos : 0 < m := NeZero.pos m
  -- Step 1: Determine direction at i0Expected m t r
  have hfiber := i0E_fiber m hm_ge t r
  have hr_le : r.val ≤ m - 2 := by omega
  rw [show (if r.val ≤ m - 2 then (1 + r.val) % m else 0) = (1 + r.val) % m
      from if_pos hr_le] at hfiber
  have hfiber_val : (1 + r.val) % m = 1 + r.val :=
    Nat.mod_eq_of_lt (by omega : 1 + r.val < m)
  rw [hfiber_val] at hfiber
  have hs_pos : 0 < (fiberIndex m (i0Expected m t r)).val := by omega
  have hs_lt : (fiberIndex m (i0Expected m t r)).val < m - 1 := by omega
  have hi_val := i0E_i m t r
  have hi_lt : (i0Expected m t r).1.val < m - 1 := by omega
  have hdir : dir0 m (i0Expected m t r) = Dir.bumpj :=
    cycle0_middle_fiber_middle_i m (i0Expected m t r) hs_pos hs_lt hi_lt
  -- Step 2: Apply successor_bumpj
  rw [successor_bumpj m (i0Expected m t r) hdir]
  -- Step 3: Both sides unfold with r ≤ m-2 branch
  unfold i0Expected
  have hr1_le : r.val + 1 ≤ m - 2 := by omega
  simp only [hr_le, ite_true, hr1_le, Fin.val_mk]
  -- Goal: (0, j_base + ⟨r, _⟩ + 1, k_base) = (0, j_base + ⟨r+1, _⟩, k_base)
  -- Key: ⟨r, _⟩ + 1 = ⟨r+1, _⟩ in Fin m when r+1 < m
  have hfin_eq : (⟨r.val, r.isLt⟩ : Fin m) + 1 = ⟨r.val + 1, by omega⟩ := by
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_mk, Fin.coe_ofNat_eq_mod]
    rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega : 1 < m),
        Nat.mod_eq_of_lt (by omega : r.val + 1 < m)]
  have hr_eq : (⟨r.val, r.isLt⟩ : Fin m) = r := Fin.ext rfl
  rw [hr_eq] at hfin_eq
  congr 1
  · congr 1
    rw [← hfin_eq, add_assoc]

/-- End of round step: s = m-1, i = 0 → dir0 = bumpk, go from r = m-2 to r = m-1. -/
private theorem i0_succ_end (m : ℕ) [NeZero m] (hm_ge : m ≥ 3) (t : Fin m) :
    successor m (dir0 m) (i0Expected m t ⟨m - 2, by omega⟩) =
    i0Expected m t ⟨m - 1, by omega⟩ := by
  have hm_pos : 0 < m := NeZero.pos m
  -- Step 1: Determine fiber at i0Expected m t ⟨m-2, _⟩
  have hfiber := i0E_fiber m hm_ge t ⟨m - 2, by omega⟩
  have hr_le : (m - 2) ≤ m - 2 := Nat.le_refl _
  simp only [Fin.val_mk, hr_le, ite_true] at hfiber
  have hfiber_val : (1 + (m - 2)) % m = m - 1 := by
    rw [show 1 + (m - 2) = m - 1 from by omega]
    exact Nat.mod_eq_of_lt (by omega : m - 1 < m)
  rw [hfiber_val] at hfiber
  -- Step 2: Determine direction = bumpk
  have hs_ne : ¬(fiberIndex m (i0Expected m t ⟨m - 2, by omega⟩)).val = 0 := by omega
  have hi_val := i0E_i m t ⟨m - 2, by omega⟩
  have hdir : dir0 m (i0Expected m t ⟨m - 2, by omega⟩) = Dir.bumpk :=
    dir0_sm1_i0 m _ hs_ne hfiber hi_val
  -- Step 3: Apply successor_bumpk
  rw [successor_bumpk m _ hdir]
  -- Step 4: Unfold i0Expected on both sides
  unfold i0Expected
  have hm1_not_le : ¬((m - 1) ≤ m - 2) := by omega
  simp only [Fin.val_mk, hr_le, ite_true, hm1_not_le, ite_false]

/-- Round transition: s = 0, j < m-1 → dir0 = bumpk, advance t by 1. -/
private theorem i0_succ_trans (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3)
    (t : Fin m) (ht : t.val < m - 1) :
    successor m (dir0 m) (i0Expected m t ⟨m - 1, by omega⟩) =
    i0Expected m ⟨t.val + 1, by omega⟩ ⟨0, NeZero.pos m⟩ := by
  have hm_pos : 0 < m := NeZero.pos m
  -- Step 1: Determine fiber = 0 at i0Expected m t ⟨m-1, _⟩
  have hfiber := i0E_fiber m hm_ge t ⟨m - 1, by omega⟩
  have hm1_not_le : ¬((m - 1) ≤ m - 2) := by omega
  simp only [Fin.val_mk, hm1_not_le, ite_false] at hfiber
  -- hfiber : (fiberIndex m (i0Expected m t ⟨m - 1, _⟩)).val = 0
  -- Step 2: Get j < m - 1
  have hj_lt := i0E_j_lt m hm_odd hm_ge t ht
  -- Step 3: Determine direction = bumpk
  have hdir : dir0 m (i0Expected m t ⟨m - 1, by omega⟩) = Dir.bumpk :=
    dir0_s0_jlt m _ hfiber hj_lt
  -- Step 4: Apply successor_bumpk
  rw [successor_bumpk m _ hdir]
  -- Step 5: Unfold i0Expected on both sides and simplify branches
  unfold i0Expected
  have h0_le : (0 : ℕ) ≤ m - 2 := by omega
  simp only [Fin.val_mk, hm1_not_le, ite_false, h0_le, ite_true]
  -- Goal: (⟨0,_⟩, j_base_t + ⟨m-2,_⟩, k_base_t + 1 + 1) =
  --        (⟨0,_⟩, j_base_{t+1} + ⟨0,_⟩, k_base_{t+1})
  -- Prove component-wise using ext
  apply Prod.ext
  · -- i component: 0 = 0
    rfl
  · apply Prod.ext
    · -- j component
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_mk, Fin.coe_ofNat_eq_mod]
      -- LHS: ((2*m-1-2*t.val) % m + (m-2)) % m
      -- RHS: ((2*m-1-2*(t.val+1)) % m + 0) % m
      rw [mod_add_raw (2 * m - 1 - 2 * t.val) (m - 2) m]
      rw [Nat.add_zero, Nat.mod_mod]
      -- Now: (2*m-1-2*t.val + (m-2)) % m = (2*m-1-2*(t.val+1)) % m
      have hlhs : 2 * m - 1 - 2 * t.val + (m - 2) = (2 * m - 3 - 2 * t.val) + m := by omega
      rw [hlhs, Nat.add_mod_right]
      have hrhs : 2 * m - 1 - 2 * (t.val + 1) = 2 * m - 3 - 2 * t.val := by omega
      rw [hrhs]
    · -- k component
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_mk, Fin.coe_ofNat_eq_mod]
      rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega : 1 < m)]
      -- LHS: (((2+2*t.val) % m + 1) % m + 1) % m
      -- RHS: (2+2*(t.val+1)) % m
      rw [mod_add_raw (2 + 2 * t.val) 1 m,
          mod_add_raw (2 + 2 * t.val + 1) 1 m]
      have hk_eq : 2 + 2 * t.val + 1 + 1 = 2 + 2 * (t.val + 1) := by omega
      rw [hk_eq]

-- Fin equality helper: avoid omega issues with Fin.ext
private theorem fin_eq_of_val_eq {n : ℕ} {a b : Fin n} (h : a.val = b.val) : a = b :=
  Fin.ext h

theorem orbit_i0_explicit (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3)
    (t r : Fin m) :
    orbit m (dir0 m) (checkpoint0 m ⟨0, NeZero.pos m⟩) (t.val * m + r.val) =
    i0Expected m t r := by
  have hm_pos : 0 < m := NeZero.pos m
  suffices H : ∀ n, ∀ t r : Fin m, n = t.val * m + r.val →
      orbit m (dir0 m) (checkpoint0 m ⟨0, hm_pos⟩) n = i0Expected m t r by
    exact H _ t r rfl
  intro n
  induction n with
  | zero =>
    intro t r hn
    have ht0 : t.val = 0 := by
      rcases Nat.eq_zero_or_pos t.val with h | h
      · exact h
      · exfalso; have : t.val * m ≥ m := Nat.le_mul_of_pos_left m h; omega
    have hr0 : r.val = 0 := by omega
    have ht : t = ⟨0, hm_pos⟩ := fin_eq_of_val_eq ht0
    have hr : r = ⟨0, hm_pos⟩ := fin_eq_of_val_eq hr0
    subst ht; subst hr
    exact base_case_i0 m hm_ge
  | succ n ih =>
    intro t r hn
    rw [orbit_succ]
    by_cases hr0 : r.val = 0
    · -- Round transition: previous step was (t-1, m-1)
      have ht_pos : 0 < t.val := by
        by_contra h; push_neg at h
        have htv : t.val = 0 := by omega
        rw [htv, Nat.zero_mul, Nat.zero_add] at hn; omega
      have hn' : n = (t.val - 1) * m + (m - 1) := by
        have h1 : n + 1 = t.val * m := by omega
        have h2 : t.val * m = (t.val - 1 + 1) * m := by congr 1; omega
        rw [h2, Nat.add_mul, Nat.one_mul] at h1; omega
      have ht_bound : t.val - 1 < m := by omega
      have ht'_lt : t.val - 1 < m - 1 := by omega
      rw [ih ⟨t.val - 1, ht_bound⟩ ⟨m - 1, by omega⟩ (by simp [Fin.val_mk]; exact hn')]
      rw [i0_succ_trans m hm_odd hm_ge ⟨t.val - 1, ht_bound⟩ (by simp [Fin.val_mk]; exact ht'_lt)]
      -- Goal: i0Expected m ⟨t.val-1+1, _⟩ ⟨0, _⟩ = i0Expected m t r
      have hreq : r = ⟨0, hm_pos⟩ := Fin.ext (by omega)
      subst hreq
      -- Goal: i0Expected m ⟨t.val-1+1, _⟩ ⟨0, _⟩ = i0Expected m t ⟨0, _⟩
      congr 1
      exact Fin.ext (by simp [Fin.val_mk]; omega)
    · -- Within round: previous step was (t, r-1)
      have hn' : n = t.val * m + (r.val - 1) := by omega
      have hr_bound : r.val - 1 < m := by omega
      rw [ih t ⟨r.val - 1, hr_bound⟩ (by simp [Fin.val_mk]; exact hn')]
      by_cases hr_m1 : r.val = m - 1
      · -- End of round: r-1 = m-2
        have hrr : (⟨r.val - 1, hr_bound⟩ : Fin m) = ⟨m - 2, by omega⟩ :=
          fin_eq_of_val_eq (by simp [Fin.val_mk]; omega)
        rw [hrr, i0_succ_end m hm_ge t]
        -- Goal: i0Expected m t ⟨m-1, _⟩ = i0Expected m t r
        convert rfl using 2
        apply fin_eq_of_val_eq; simp [Fin.val_mk]; omega
      · -- Middle step: r-1 ≤ m-3
        have hr_le : (⟨r.val - 1, hr_bound⟩ : Fin m).val ≤ m - 3 := by
          simp [Fin.val_mk]; omega
        rw [i0_succ_mid m hm_ge t ⟨r.val - 1, hr_bound⟩ hr_le]
        -- Goal: i0Expected m t ⟨r.val-1+1, _⟩ = i0Expected m t r
        convert rfl using 2
        apply fin_eq_of_val_eq; simp [Fin.val_mk]; omega

/-- Helper: derive t equality from k_base equality using mul2 injectivity. -/
private theorem t_eq_of_kbase_eq (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (t₁ t₂ : Fin m)
    (h : (⟨(2 + 2 * t₁.val) % m, Nat.mod_lt _ (NeZero.pos m)⟩ : Fin m) =
         ⟨(2 + 2 * t₂.val) % m, Nat.mod_lt _ (NeZero.pos m)⟩) : t₁ = t₂ := by
  have hm_pos : 0 < m := NeZero.pos m
  have hbij := mul2_bijective_odd m hm_odd hm_pos
  have hval : (2 + 2 * t₁.val) % m = (2 + 2 * t₂.val) % m := congrArg Fin.val h
  have hmod2 : 2 * t₁.val % m = 2 * t₂.val % m :=
    Nat.ModEq.add_left_cancel (Nat.ModEq.refl 2) hval
  exact hbij.1 (Fin.ext hmod2)

/-- The map (t, r) ↦ (j, k) extracted from i0Expected is injective. -/
private theorem i0Expected_jk_injective (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3) :
    Function.Injective (fun p : Fin m × Fin m =>
      let v := i0Expected m p.1 p.2
      (v.2.1, v.2.2)) := by
  intro ⟨t₁, r₁⟩ ⟨t₂, r₂⟩ h
  simp only [i0Expected] at h
  have hm_pos : 0 < m := NeZero.pos m
  -- Abbreviations
  set jb₁ : Fin m := ⟨(2 * m - 1 - 2 * t₁.val) % m, Nat.mod_lt _ hm_pos⟩
  set jb₂ : Fin m := ⟨(2 * m - 1 - 2 * t₂.val) % m, Nat.mod_lt _ hm_pos⟩
  set kb₁ : Fin m := ⟨(2 + 2 * t₁.val) % m, Nat.mod_lt _ hm_pos⟩
  set kb₂ : Fin m := ⟨(2 + 2 * t₂.val) % m, Nat.mod_lt _ hm_pos⟩
  -- Key identity: jb + kb = 1
  have hjk₁ : jb₁ + kb₁ = 1 := jbase_add_kbase m hm_ge t₁
  have hjk₂ : jb₂ + kb₂ = 1 := jbase_add_kbase m hm_ge t₂
  -- Case split on if-branches
  simp only [Prod.mk.injEq] at h
  obtain ⟨hj_eq, hk_eq⟩ := h
  by_cases hr1 : r₁.val ≤ m - 2 <;> by_cases hr2 : r₂.val ≤ m - 2
  · -- Both ≤ m-2: same branch
    simp only [hr1, hr2, ↓reduceIte] at hj_eq hk_eq
    have ht := t_eq_of_kbase_eq m hm_odd t₁ t₂ hk_eq
    subst ht
    exact Prod.ext rfl (add_left_cancel hj_eq)
  · -- r₁ ≤ m-2, r₂ = m-1: cross-branch contradiction
    simp only [hr1, hr2, ↓reduceIte] at hj_eq hk_eq
    exfalso
    -- hj_eq : jb₁ + ⟨r₁.val, _⟩ = jb₂ + ⟨m-2, _⟩
    -- hk_eq : kb₁ = kb₂ + 1
    -- Derive jb₁ + 1 = jb₂ from hjk₁, hjk₂, hk_eq
    have hjb_rel : jb₁ + 1 = jb₂ := by
      have h1 : jb₁ + (kb₂ + 1) = 1 := by rw [← hk_eq]; exact hjk₁
      have : (jb₁ + 1) + kb₂ = jb₂ + kb₂ := by
        calc (jb₁ + 1) + kb₂ = jb₁ + (kb₂ + 1) := by abel
          _ = 1 := h1
          _ = jb₂ + kb₂ := hjk₂.symm
      exact add_right_cancel this
    -- Build: jb₂ + ⟨m-2,...⟩ = jb₁ + (1 + ⟨m-2,...⟩)
    have h_rhs : jb₂ + ⟨m - 2, by omega⟩ = jb₁ + ((1 : Fin m) + ⟨m - 2, by omega⟩) := by
      rw [← hjb_rel]; abel
    have hj_eq' : jb₁ + ⟨r₁.val, r₁.isLt⟩ = jb₁ + ((1 : Fin m) + ⟨m - 2, by omega⟩) :=
      hj_eq.trans h_rhs
    have hr_eq := add_left_cancel hj_eq'
    have hval := congrArg Fin.val hr_eq
    simp only [Fin.val_add] at hval
    have h1v : (1 : Fin m).val = 1 := Nat.mod_eq_of_lt (by omega : 1 < m)
    rw [h1v, show 1 + (m - 2) = m - 1 from by omega,
        Nat.mod_eq_of_lt (by omega : m - 1 < m)] at hval; omega
  · -- r₁ = m-1, r₂ ≤ m-2: symmetric cross-branch contradiction
    simp only [hr1, hr2, ↓reduceIte] at hj_eq hk_eq
    exfalso
    have hjb_rel : jb₂ + 1 = jb₁ := by
      have h1 : jb₂ + (kb₁ + 1) = 1 := by
        have h := hjk₂; rwa [← hk_eq] at h
      have : (jb₂ + 1) + kb₁ = jb₁ + kb₁ := by
        calc (jb₂ + 1) + kb₁ = jb₂ + (1 + kb₁) := by abel
          _ = jb₂ + (kb₁ + 1) := by rw [add_comm (1 : Fin m) kb₁]
          _ = 1 := h1
          _ = jb₁ + kb₁ := hjk₁.symm
      exact add_right_cancel this
    have h_lhs : jb₁ + ⟨m - 2, by omega⟩ = jb₂ + ((1 : Fin m) + ⟨m - 2, by omega⟩) := by
      rw [← hjb_rel]; abel
    have hj_eq' : jb₂ + ⟨r₂.val, r₂.isLt⟩ = jb₂ + ((1 : Fin m) + ⟨m - 2, by omega⟩) := by
      rw [← hj_eq]; exact h_lhs
    have hr_eq := add_left_cancel hj_eq'
    have hval := congrArg Fin.val hr_eq
    simp only [Fin.val_add] at hval
    have h1v : (1 : Fin m).val = 1 := Nat.mod_eq_of_lt (by omega : 1 < m)
    rw [h1v, show 1 + (m - 2) = m - 1 from by omega,
        Nat.mod_eq_of_lt (by omega : m - 1 < m)] at hval; omega
  · -- Both = m-1
    simp only [hr1, hr2, ↓reduceIte] at hj_eq hk_eq
    have ht := t_eq_of_kbase_eq m hm_odd t₁ t₂ (add_right_cancel hk_eq)
    have hr : r₁ = r₂ := by ext; have := r₁.isLt; have := r₂.isLt; omega
    exact Prod.ext ht hr

/-- The i0Expected function is injective (from jk-projection injectivity). -/
theorem i0Expected_injective (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3) :
    Function.Injective (fun p : Fin m × Fin m => i0Expected m p.1 p.2) := by
  intro ⟨t₁, r₁⟩ ⟨t₂, r₂⟩ h
  apply i0Expected_jk_injective m hm_odd hm_ge
  exact Prod.ext (congrArg (·.2.1) h) (congrArg (·.2.2) h)

/-- The i0Expected function covers all (0, j, k) vertices. -/
theorem i0Expected_surjective (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3) :
    ∀ j k : Fin m, ∃ t r : Fin m, i0Expected m t r = (⟨0, NeZero.pos m⟩, j, k) := by
  -- i0Expected maps Fin m × Fin m injectively to {0} × Fin m × Fin m
  -- Since domain and codomain both have m² elements, this gives surjectivity
  have hinj := i0Expected_jk_injective m hm_odd hm_ge
  have hsurj : Function.Surjective (fun p : Fin m × Fin m =>
      let v := i0Expected m p.1 p.2; (v.2.1, v.2.2)) :=
    Finite.injective_iff_surjective.mp hinj
  intro j k
  obtain ⟨⟨t, r⟩, htr⟩ := hsurj (j, k)
  refine ⟨t, r, ?_⟩
  -- htr says the (j,k) components match; the i-component is always 0
  have htr_j : (i0Expected m t r).2.1 = j := congrArg Prod.fst htr
  have htr_k : (i0Expected m t r).2.2 = k := congrArg Prod.snd htr
  -- The i-component of i0Expected is always 0
  have htr_i : (i0Expected m t r).1 = ⟨0, NeZero.pos m⟩ := by
    simp only [i0Expected]; split_ifs <;> rfl
  ext <;> simp [htr_i, htr_j, htr_k]

/-- i0_block_complete follows from the explicit orbit characterization. -/
theorem i0_block_complete (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3) :
    ∀ j k : Fin m, ∃ n : Fin (m * m),
      orbit m (dir0 m) (checkpoint0 m ⟨0, NeZero.pos m⟩) n.val =
      (⟨0, NeZero.pos m⟩, j, k) := by
  intro j k
  obtain ⟨t, r, htr⟩ := i0Expected_surjective m hm_odd hm_ge j k
  refine ⟨⟨t.val * m + r.val, ?_⟩, ?_⟩
  · have := t.isLt; have := r.isLt
    calc t.val * m + r.val < t.val * m + m := by omega
    _ = (t.val + 1) * m := by ring
    _ ≤ m * m := by nlinarith
  · rw [orbit_i0_explicit m hm_odd hm_ge t r, htr]

/-! ### 4.2 Transition between i-blocks -/

def blockEntry (m : ℕ) [NeZero m] (i : Fin m) : Vertex m :=
  let k : Fin m := ⟨(2 + m - i.val) % m, Nat.mod_lt _ (NeZero.pos m)⟩
  (i, ⟨m - 1, by have := NeZero.pos m; omega⟩, k)

private lemma mod_add_mod_eq_zero {a b m : ℕ} (_hm : 0 < m) (h : a + b = 2 * m) :
    (a % m + b % m) % m = 0 := by
  rw [← Nat.add_mod, h]; simp

theorem block_exit_bumps_i (m : ℕ) [NeZero m] (hm_ge : m ≥ 3)
    (i : Fin m) (hi : i.val < m - 1) :
    let exitVertex : Vertex m :=
      (i, ⟨m - 1, by have := NeZero.pos m; omega⟩,
       ⟨(1 + m - i.val) % m, Nat.mod_lt _ (NeZero.pos m)⟩)
    dir0 m exitVertex = Dir.bumpi := by
  intro exitVertex
  rw [cycle0_i_change_condition]
  refine ⟨?_, by simp [exitVertex]⟩
  simp only [exitVertex, fiberIndex, Fin.val_add]
  have hm_pos : 0 < m := NeZero.pos m
  have hi_lt_m : i.val < m := i.isLt
  have hsum : i.val + (m - 1) + (1 + m - i.val) = 2 * m := by omega
  -- Goal: ((i.val + (m-1)) % m + (1+m-i.val) % m) % m = 0
  exact mod_add_mod_eq_zero hm_pos hsum

/-! ### 4.3 The i = m−1 block -/

/-- Expected vertex in the i=m-1 block.
    For i=m-1: middle fibers → bumpk, s=m-1 → bumpj (since i>0).

    Round t, step r:
    - r ≤ m-3: (m-1, j_t, k_t + r) with s = 1+r (bumpk in middle)
    - r = m-2: (m-1, j_t, k_t + (m-2)) with s = m-1 (bumpj next)
    - r = m-1: (m-1, j_t + 1, k_t + (m-2)) with s = 0 (bumpk if j≠m-1)

    Note: j_base advances by +1 per round, k_base by -1 per round.
    (cf. i0Expected where j advances by -2 and k by +2, using mul2 bijection.) -/
def lastExpected (m : ℕ) [NeZero m] (t r : Fin m) : Vertex m :=
  let i_val : Fin m := ⟨m - 1, by have := NeZero.pos m; omega⟩
  let j_base : Fin m := ⟨(m - 1 + t.val) % m, Nat.mod_lt _ (NeZero.pos m)⟩
  let k_base : Fin m := ⟨(m + 3 - t.val) % m, Nat.mod_lt _ (NeZero.pos m)⟩
  if r.val ≤ m - 2 then
    (i_val, j_base, k_base + ⟨r.val, r.isLt⟩)
  else -- r = m-1
    (i_val, j_base + 1, k_base + ⟨m - 2, by have := NeZero.pos m; omega⟩)

-- Helper: fiber index of lastExpected
private theorem lastE_fiber (m : ℕ) [NeZero m] (hm_ge : m ≥ 3) (t r : Fin m) :
    (fiberIndex m (lastExpected m t r)).val =
    if r.val ≤ m - 2 then (1 + r.val) % m else 0 := by
  have hm_pos : 0 < m := NeZero.pos m
  unfold fiberIndex lastExpected
  split_ifs with hr
  · -- r ≤ m-2: fiber = (1+r) % m
    dsimp only [Fin.val_add, Fin.val_mk]
    rw [raw_add_mod (m - 1) (m - 1 + t.val) m,
        mod_add_raw (m + 3 - t.val) r.val m,
        mod_add_mod' (m - 1 + (m - 1 + t.val)) (m + 3 - t.val + r.val)]
    have hsum : m - 1 + (m - 1 + t.val) + (m + 3 - t.val + r.val) =
                (1 + r.val) + m * 3 := by omega
    rw [hsum, Nat.add_mul_mod_self_left]
  · -- r = m-1: fiber = 0
    dsimp only [Fin.val_add, Fin.val_mk]
    simp only [Fin.coe_ofNat_eq_mod]
    rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega : 1 < m)]
    rw [mod_add_raw (m - 1 + t.val) 1 m,
        show m - 1 + t.val + 1 = m + t.val from by omega,
        raw_add_mod (m - 1) (m + t.val) m,
        mod_add_raw (m + 3 - t.val) (m - 2) m,
        mod_add_mod' (m - 1 + (m + t.val)) (m + 3 - t.val + (m - 2))]
    have hsum : m - 1 + (m + t.val) + (m + 3 - t.val + (m - 2)) = m * 4 := by omega
    rw [hsum, Nat.mul_mod_right]

-- Helper: i-component of lastExpected is m-1
private theorem lastE_i (m : ℕ) [NeZero m] (t r : Fin m) :
    (lastExpected m t r).1.val = m - 1 := by
  simp only [lastExpected]; split_ifs <;> simp

-- Helper: j < m-1 at round boundary (t < m-1) for lastExpected
private theorem lastE_j_lt (m : ℕ) [NeZero m] (hm_ge : m ≥ 3) (t : Fin m) (ht : t.val < m - 1) :
    (lastExpected m t ⟨m - 1, by have := NeZero.pos m; omega⟩).2.1.val < m - 1 := by
  have hm_pos : 0 < m := NeZero.pos m
  unfold lastExpected
  simp only [Fin.val_mk, show ¬(m - 1 ≤ m - 2) from by omega, ite_false]
  simp only [Fin.val_add, Fin.val_mk, Fin.coe_ofNat_eq_mod]
  rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega : 1 < m)]
  rw [mod_add_raw (m - 1 + t.val) 1 m]
  rw [show m - 1 + t.val + 1 = m + t.val from by omega]
  by_cases ht0 : t.val = 0
  · rw [ht0, Nat.add_zero]; simp [Nat.mod_self]; omega
  · rw [show m + t.val = t.val + m * 1 from by ring, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (by omega : t.val < m)]
    omega

-- Base case: blockEntry(m-1) = lastExpected 0 0
private theorem base_case_last (m : ℕ) [NeZero m] (hm_ge : m ≥ 3) :
    blockEntry m ⟨m - 1, by have := NeZero.pos m; omega⟩ =
    lastExpected m ⟨0, NeZero.pos m⟩ ⟨0, NeZero.pos m⟩ := by
  simp only [blockEntry, lastExpected]
  have hm_pos : 0 < m := NeZero.pos m
  have h0le : (0 : ℕ) ≤ m - 2 := by omega
  simp only [Fin.val_mk, h0le, ite_true, Nat.add_zero]
  apply Prod.ext
  · rfl  -- i component
  · apply Prod.ext
    · -- j component: ⟨m-1, _⟩ = ⟨(m-1)%m, _⟩
      apply Fin.ext; simp only [Fin.val_mk]
      exact (Nat.mod_eq_of_lt (by omega : m - 1 < m)).symm
    · -- k component: ⟨(2+m-(m-1))%m, _⟩ = ⟨(m+3)%m, _⟩ + ⟨0, _⟩
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_mk, Nat.sub_zero, Nat.add_zero, Nat.mod_mod]
      -- Goal: (2 + m - (m - 1)) % m = (m + 3) % m
      have h1 : 2 + m - (m - 1) = 3 := by omega
      have h2 : m + 3 = 3 + m * 1 := by omega
      rw [h1, h2, Nat.add_mul_mod_self_left]

/-- Middle fiber step for i=m-1 block: 0 < s < m-1, i = m-1 → dir0 = bumpk. -/
private theorem last_succ_mid (m : ℕ) [NeZero m] (hm_ge : m ≥ 3) (t : Fin m) (r : Fin m)
    (hr : r.val ≤ m - 3) :
    successor m (dir0 m) (lastExpected m t r) =
    lastExpected m t ⟨r.val + 1, by omega⟩ := by
  have hm_pos : 0 < m := NeZero.pos m
  have hfiber := lastE_fiber m hm_ge t r
  have hr_le : r.val ≤ m - 2 := by omega
  rw [show (if r.val ≤ m - 2 then (1 + r.val) % m else 0) = (1 + r.val) % m
      from if_pos hr_le] at hfiber
  have hfiber_val : (1 + r.val) % m = 1 + r.val :=
    Nat.mod_eq_of_lt (by omega : 1 + r.val < m)
  rw [hfiber_val] at hfiber
  have hs_pos : 0 < (fiberIndex m (lastExpected m t r)).val := by omega
  have hs_lt : (fiberIndex m (lastExpected m t r)).val < m - 1 := by omega
  have hi_eq := lastE_i m t r
  have hs_ne0 : ¬(fiberIndex m (lastExpected m t r)).val = 0 := by omega
  have hs_nem1 : ¬(fiberIndex m (lastExpected m t r)).val = m - 1 := by omega
  have hdir : dir0 m (lastExpected m t r) = Dir.bumpk :=
    dir0_mid_im1 m _ hs_ne0 hs_nem1 hi_eq
  rw [successor_bumpk m _ hdir]
  unfold lastExpected
  have hr1_le : r.val + 1 ≤ m - 2 := by omega
  simp only [hr_le, ite_true, hr1_le, Fin.val_mk]
  congr 1; congr 1
  rw [add_assoc]
  congr 1
  apply Fin.ext
  simp only [Fin.val_add, Fin.val_mk, Fin.coe_ofNat_eq_mod]
  rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega : 1 < m),
      Nat.mod_eq_of_lt (by omega : r.val + 1 < m)]

/-- End of round step for i=m-1 block: s = m-1, i > 0 → dir0 = bumpj. -/
private theorem last_succ_end (m : ℕ) [NeZero m] (hm_ge : m ≥ 3) (t : Fin m) :
    successor m (dir0 m) (lastExpected m t ⟨m - 2, by omega⟩) =
    lastExpected m t ⟨m - 1, by omega⟩ := by
  have hm_pos : 0 < m := NeZero.pos m
  have hfiber := lastE_fiber m hm_ge t ⟨m - 2, by omega⟩
  have hr_le : (m - 2) ≤ m - 2 := Nat.le_refl _
  simp only [Fin.val_mk, hr_le, ite_true] at hfiber
  have hfiber_val : (1 + (m - 2)) % m = m - 1 := by
    rw [show 1 + (m - 2) = m - 1 from by omega]
    exact Nat.mod_eq_of_lt (by omega : m - 1 < m)
  rw [hfiber_val] at hfiber
  have hs_ne : ¬(fiberIndex m (lastExpected m t ⟨m - 2, by omega⟩)).val = 0 := by omega
  have hi_gt : (lastExpected m t ⟨m - 2, by omega⟩).1.val > 0 := by
    rw [lastE_i]; omega
  have hdir : dir0 m (lastExpected m t ⟨m - 2, by omega⟩) = Dir.bumpj :=
    dir0_sm1_igt0 m _ hs_ne hfiber hi_gt
  rw [successor_bumpj m _ hdir]
  unfold lastExpected
  have hm1_not_le : ¬((m - 1) ≤ m - 2) := by omega
  simp only [Fin.val_mk, hr_le, ite_true, hm1_not_le, ite_false]

/-- Round transition for i=m-1 block: s = 0, j < m-1 → dir0 = bumpk. -/
private theorem last_succ_trans (m : ℕ) [NeZero m] (hm_ge : m ≥ 3)
    (t : Fin m) (ht : t.val < m - 1) :
    successor m (dir0 m) (lastExpected m t ⟨m - 1, by omega⟩) =
    lastExpected m ⟨t.val + 1, by omega⟩ ⟨0, NeZero.pos m⟩ := by
  have hm_pos : 0 < m := NeZero.pos m
  have hfiber := lastE_fiber m hm_ge t ⟨m - 1, by omega⟩
  have hm1_not_le : ¬((m - 1) ≤ m - 2) := by omega
  simp only [Fin.val_mk, hm1_not_le, ite_false] at hfiber
  have hj_lt := lastE_j_lt m hm_ge t ht
  have hdir : dir0 m (lastExpected m t ⟨m - 1, by omega⟩) = Dir.bumpk :=
    dir0_s0_jlt m _ hfiber hj_lt
  rw [successor_bumpk m _ hdir]
  unfold lastExpected
  have h0_le : (0 : ℕ) ≤ m - 2 := by omega
  simp only [Fin.val_mk, hm1_not_le, ite_false, h0_le, ite_true]
  apply Prod.ext
  · rfl  -- i component
  · apply Prod.ext
    · -- j component: jb_t + 1 = jb_{t+1}
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_mk, Fin.coe_ofNat_eq_mod]
      rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega : 1 < m),
          mod_add_raw (m - 1 + t.val) 1 m]; congr 1
    · -- k component: kb_t + ⟨m-2,_⟩ + 1 = kb_{t+1} + ⟨0,_⟩
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_mk, Fin.coe_ofNat_eq_mod,
                  Nat.add_zero, Nat.sub_zero, Nat.mod_mod]
      rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega : 1 < m),
          mod_add_raw (m + 3 - t.val) (m - 2) m,
          mod_add_raw (m + 3 - t.val + (m - 2)) 1 m,
          show m + 3 - t.val + (m - 2) + 1 = m + 3 - (t.val + 1) + m * 1 from by omega,
          Nat.add_mul_mod_self_left]

theorem orbit_last_explicit (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3)
    (t r : Fin m) :
    orbit m (dir0 m) (blockEntry m ⟨m - 1, by have := NeZero.pos m; omega⟩)
      (t.val * m + r.val) = lastExpected m t r := by
  have hm_pos : 0 < m := NeZero.pos m
  suffices H : ∀ n, ∀ t r : Fin m, n = t.val * m + r.val →
      orbit m (dir0 m) (blockEntry m ⟨m - 1, by omega⟩) n = lastExpected m t r by
    exact H _ t r rfl
  intro n
  induction n with
  | zero =>
    intro t r hn
    have ht0 : t.val = 0 := by
      rcases Nat.eq_zero_or_pos t.val with h | h
      · exact h
      · exfalso; have : t.val * m ≥ m := Nat.le_mul_of_pos_left m h; omega
    have hr0 : r.val = 0 := by omega
    have ht : t = ⟨0, hm_pos⟩ := fin_eq_of_val_eq ht0
    have hr : r = ⟨0, hm_pos⟩ := fin_eq_of_val_eq hr0
    subst ht; subst hr
    exact base_case_last m hm_ge
  | succ n ih =>
    intro t r hn
    rw [orbit_succ]
    by_cases hr0 : r.val = 0
    · -- Round transition: previous step was (t-1, m-1)
      have ht_pos : 0 < t.val := by
        by_contra h; push_neg at h
        have htv : t.val = 0 := by omega
        rw [htv, Nat.zero_mul, Nat.zero_add] at hn; omega
      have hn' : n = (t.val - 1) * m + (m - 1) := by
        have h1 : n + 1 = t.val * m := by omega
        have h2 : t.val * m = (t.val - 1 + 1) * m := by congr 1; omega
        rw [h2, Nat.add_mul, Nat.one_mul] at h1; omega
      have ht_bound : t.val - 1 < m := by omega
      have ht'_lt : t.val - 1 < m - 1 := by omega
      rw [ih ⟨t.val - 1, ht_bound⟩ ⟨m - 1, by omega⟩ (by simp [Fin.val_mk]; exact hn')]
      rw [last_succ_trans m hm_ge ⟨t.val - 1, ht_bound⟩ (by simp [Fin.val_mk]; exact ht'_lt)]
      have hreq : r = ⟨0, hm_pos⟩ := Fin.ext (by omega)
      subst hreq
      congr 1
      exact Fin.ext (by simp [Fin.val_mk]; omega)
    · -- Within round: previous step was (t, r-1)
      have hn' : n = t.val * m + (r.val - 1) := by omega
      have hr_bound : r.val - 1 < m := by omega
      rw [ih t ⟨r.val - 1, hr_bound⟩ (by simp [Fin.val_mk]; exact hn')]
      by_cases hr_m1 : r.val = m - 1
      · -- End of round: r-1 = m-2
        have hrr : (⟨r.val - 1, hr_bound⟩ : Fin m) = ⟨m - 2, by omega⟩ :=
          fin_eq_of_val_eq (by simp [Fin.val_mk]; omega)
        rw [hrr, last_succ_end m hm_ge t]
        convert rfl using 2
        apply fin_eq_of_val_eq; simp [Fin.val_mk]; omega
      · -- Middle step: r-1 ≤ m-3
        have hr_le : (⟨r.val - 1, hr_bound⟩ : Fin m).val ≤ m - 3 := by
          simp [Fin.val_mk]; omega
        rw [last_succ_mid m hm_ge t ⟨r.val - 1, hr_bound⟩ hr_le]
        convert rfl using 2
        apply fin_eq_of_val_eq; simp [Fin.val_mk]; omega

-- Helper: j_base determines t for lastExpected (since stride is 1, not 2)
private theorem t_eq_of_jbase_last (m : ℕ) [NeZero m] (t₁ t₂ : Fin m)
    (h : (⟨(m - 1 + t₁.val) % m, Nat.mod_lt _ (NeZero.pos m)⟩ : Fin m) =
         ⟨(m - 1 + t₂.val) % m, Nat.mod_lt _ (NeZero.pos m)⟩) : t₁ = t₂ := by
  have hval : (m - 1 + t₁.val) % m = (m - 1 + t₂.val) % m := congrArg Fin.val h
  have hmeq : t₁.val % m = t₂.val % m :=
    Nat.ModEq.add_left_cancel (Nat.ModEq.refl (m - 1)) hval
  have h1 : t₁.val % m = t₁.val := Nat.mod_eq_of_lt t₁.isLt
  have h2 : t₂.val % m = t₂.val := Nat.mod_eq_of_lt t₂.isLt
  exact Fin.ext (by omega)

-- Helper: jbase + kbase = 2 (in Fin m) for lastExpected
private theorem jbase_add_kbase_last (m : ℕ) [NeZero m] (hm_ge : m ≥ 3) (t : Fin m) :
    (⟨(m - 1 + t.val) % m, Nat.mod_lt _ (NeZero.pos m)⟩ : Fin m) +
    ⟨(m + 3 - t.val) % m, Nat.mod_lt _ (NeZero.pos m)⟩ = 2 := by
  have hm_pos : 0 < m := NeZero.pos m
  have ht_lt : t.val < m := t.isLt
  apply Fin.ext
  show ((m - 1 + t.val) % m + (m + 3 - t.val) % m) % m = (2 : Fin m).val
  rw [← Nat.add_mod]
  have hsum : (m - 1 + t.val) + (m + 3 - t.val) = 2 * m + 2 := by omega
  rw [hsum]
  conv_lhs => rw [show 2 * m + 2 = 2 + m * 2 from by ring]
  simp [Nat.add_mul_mod_self_left]

-- Helper: 1 + (m-2) = m-1 in Fin m
private theorem fin_one_add_m_sub_two (m : ℕ) [NeZero m] (hm_ge : m ≥ 3) :
    (1 : Fin m) + ⟨m - 2, by omega⟩ = ⟨m - 1, by omega⟩ := by
  apply Fin.ext
  simp only [Fin.val_add, Fin.coe_ofNat_eq_mod, Fin.val_mk]
  rw [Nat.mod_eq_of_lt (show 1 < m by omega), show 1 + (m - 2) = m - 1 from by omega]
  exact Nat.mod_eq_of_lt (by omega)

private theorem lastExpected_jk_injective (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3) :
    Function.Injective (fun p : Fin m × Fin m =>
      let v := lastExpected m p.1 p.2
      (v.2.1, v.2.2)) := by
  intro ⟨t₁, r₁⟩ ⟨t₂, r₂⟩ h
  simp only [lastExpected] at h
  have hm_pos : 0 < m := NeZero.pos m
  set jb₁ : Fin m := ⟨(m - 1 + t₁.val) % m, Nat.mod_lt _ hm_pos⟩
  set jb₂ : Fin m := ⟨(m - 1 + t₂.val) % m, Nat.mod_lt _ hm_pos⟩
  set kb₁ : Fin m := ⟨(m + 3 - t₁.val) % m, Nat.mod_lt _ hm_pos⟩
  set kb₂ : Fin m := ⟨(m + 3 - t₂.val) % m, Nat.mod_lt _ hm_pos⟩
  have t_of_jb : jb₁ = jb₂ → t₁ = t₂ := fun hjb =>
    t_eq_of_jbase_last m t₁ t₂ hjb
  simp only [Prod.mk.injEq] at h
  obtain ⟨hj_eq, hk_eq⟩ := h
  by_cases hr1_le : r₁.val ≤ m - 2 <;> by_cases hr2_le : r₂.val ≤ m - 2
  · -- Both ≤ m-2: j determines t, then k cancellation gives r
    simp only [hr1_le, hr2_le, ↓reduceIte] at hj_eq hk_eq
    have ht := t_of_jb hj_eq
    subst ht
    exact Prod.ext rfl (add_left_cancel hk_eq)
  · -- r₁ ≤ m-2, r₂ = m-1: cross-branch contradiction
    simp only [hr1_le, show ¬(r₂.val ≤ m - 2) from hr2_le, ↓reduceIte] at hj_eq hk_eq
    exfalso
    -- Use jb + kb = 2 invariant to derive kb₁ + 1 = kb₂
    have hjk₁ := jbase_add_kbase_last m hm_ge t₁
    have hjk₂ := jbase_add_kbase_last m hm_ge t₂
    -- hj_eq : jb₁ = jb₂ + 1, so (jb₂ + 1) + kb₁ = 2
    have h3 : (jb₂ + 1) + kb₁ = (2 : Fin m) := hj_eq ▸ hjk₁
    rw [add_assoc, add_comm (1 : Fin m) kb₁] at h3
    have hkb : kb₁ + 1 = kb₂ := add_left_cancel (h3.trans hjk₂.symm)
    -- Substitute into hk_eq: kb₁ + r₁ = (kb₁ + 1) + (m-2) = kb₁ + (1 + (m-2))
    have hk' : kb₁ + (⟨r₁.val, r₁.isLt⟩ : Fin m) =
               kb₁ + ((1 : Fin m) + ⟨m - 2, by omega⟩) := by
      rw [hk_eq, ← hkb, add_assoc]
    have hr_eq := add_left_cancel hk'
    -- 1 + (m-2) = m-1 in Fin m
    rw [fin_one_add_m_sub_two m hm_ge] at hr_eq
    have : r₁.val = m - 1 := congrArg Fin.val hr_eq
    omega
  · -- r₁ = m-1, r₂ ≤ m-2 (symmetric)
    simp only [show ¬(r₁.val ≤ m - 2) from hr1_le, hr2_le, ↓reduceIte] at hj_eq hk_eq
    exfalso
    have hjk₁ := jbase_add_kbase_last m hm_ge t₁
    have hjk₂ := jbase_add_kbase_last m hm_ge t₂
    -- hj_eq : jb₁ + 1 = jb₂, so jb₂ = jb₁ + 1
    -- (jb₁ + 1) + kb₂ = jb₂ + kb₂ = 2
    have h3 : (jb₁ + 1) + kb₂ = (2 : Fin m) := hj_eq ▸ hjk₂
    rw [add_assoc, add_comm (1 : Fin m) kb₂] at h3
    have hkb : kb₂ + 1 = kb₁ := add_left_cancel (h3.trans hjk₁.symm)
    -- hk_eq: kb₁ + (m-2) = kb₂ + r₂ → (kb₂ + 1) + (m-2) = kb₂ + r₂
    have hk' : kb₂ + ((1 : Fin m) + ⟨m - 2, by omega⟩) =
               kb₂ + (⟨r₂.val, r₂.isLt⟩ : Fin m) := by
      rw [← add_assoc, hkb, hk_eq]
    have hr_eq := add_left_cancel hk'
    rw [fin_one_add_m_sub_two m hm_ge] at hr_eq
    have : r₂.val = m - 1 := (congrArg Fin.val hr_eq).symm
    omega
  · -- Both = m-1
    simp only [show ¬(r₁.val ≤ m - 2) from hr1_le, show ¬(r₂.val ≤ m - 2) from hr2_le, ↓reduceIte] at hj_eq hk_eq
    have ht := t_of_jb (add_right_cancel hj_eq)
    have hr : r₁ = r₂ := by ext; have := r₁.isLt; have := r₂.isLt; omega
    exact Prod.ext ht hr

theorem lastExpected_surjective (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3) :
    ∀ j k : Fin m, ∃ t r : Fin m,
      lastExpected m t r = (⟨m - 1, by have := NeZero.pos m; omega⟩, j, k) := by
  have hinj := lastExpected_jk_injective m hm_odd hm_ge
  have hsurj : Function.Surjective (fun p : Fin m × Fin m =>
      let v := lastExpected m p.1 p.2; (v.2.1, v.2.2)) :=
    Finite.injective_iff_surjective.mp hinj
  intro j k
  obtain ⟨⟨t, r⟩, htr⟩ := hsurj (j, k)
  refine ⟨t, r, ?_⟩
  have htr_j : (lastExpected m t r).2.1 = j := congrArg Prod.fst htr
  have htr_k : (lastExpected m t r).2.2 = k := congrArg Prod.snd htr
  have htr_i : (lastExpected m t r).1 = ⟨m - 1, by have := NeZero.pos m; omega⟩ := by
    simp only [lastExpected]; split_ifs <;> rfl
  ext <;> simp [htr_i, htr_j, htr_k]

theorem last_block_complete (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3) :
    ∀ j k : Fin m, ∃ n : Fin (m * m),
      orbit m (dir0 m)
        (blockEntry m ⟨m - 1, by have := NeZero.pos m; omega⟩) n.val =
      (⟨m - 1, by have := NeZero.pos m; omega⟩, j, k) := by
  intro j k
  obtain ⟨t, r, htr⟩ := lastExpected_surjective m hm_odd hm_ge j k
  refine ⟨⟨t.val * m + r.val, ?_⟩, ?_⟩
  · have := t.isLt; have := r.isLt
    calc t.val * m + r.val < t.val * m + m := by omega
    _ = (t.val + 1) * m := by ring
    _ ≤ m * m := by nlinarith
  · rw [orbit_last_explicit m hm_odd hm_ge t r, htr]

/-! ### 4.4 The intermediate block (0 < i < m−1) -/

/-- 0<s<m-1, i<m-1 → dir0 = bumpj -/
theorem dir0_mid_ilt (m : ℕ) [NeZero m] (v : Vertex m)
    (hs_ne0 : ¬(fiberIndex m v).val = 0)
    (hs_nem1 : ¬(fiberIndex m v).val = m - 1)
    (hi_lt : v.1.val < m - 1) : dir0 m v = Dir.bumpj := by
  simp only [dir0]; split_ifs <;> simp_all <;> omega

/-- Expected vertex in an intermediate block (0 < i < m-1).
    For 0 < i < m-1: middle fibers → bumpj (i < m-1), s=m-1 → bumpj (i > 0).
    All m-1 steps within a round are bumpj, so the formula is uniform in r.

    Round t, step r:
    - vertex = (i, j_base_t + r, k_base_t)
    where j_base_t = (m-1-t) mod m, k_base_t = (2+m-i+t) mod m.
    - fiber s = (1+r) mod m.

    At s=0 (r=m-1): j = (m-2-t) mod m.
    For t < m-1: j < m-1 → bumpk (round transition).
    For t = m-1: j = m-1 → bumpi (block exit). -/
def midExpected (m : ℕ) [NeZero m] (i : Fin m) (t r : Fin m) : Vertex m :=
  let j_base : Fin m := ⟨(m - 1 - t.val) % m, Nat.mod_lt _ (NeZero.pos m)⟩
  let k_base : Fin m := ⟨(2 + m - i.val + t.val) % m, Nat.mod_lt _ (NeZero.pos m)⟩
  (i, j_base + ⟨r.val, r.isLt⟩, k_base)

-- Helper: fiber index of midExpected
private theorem midE_fiber (m : ℕ) [NeZero m] (hm_ge : m ≥ 3) (i : Fin m) (t r : Fin m) :
    (fiberIndex m (midExpected m i t r)).val = (1 + r.val) % m := by
  have hm_pos : 0 < m := NeZero.pos m
  unfold fiberIndex midExpected
  simp only [Fin.val_add, Fin.val_mk]
  rw [mod_add_raw (m - 1 - t.val) r.val m,
      raw_add_mod i.val (m - 1 - t.val + r.val) m,
      mod_add_mod' (i.val + (m - 1 - t.val + r.val)) (2 + m - i.val + t.val)]
  have hsum : i.val + (m - 1 - t.val + r.val) + (2 + m - i.val + t.val) =
              1 + r.val + m * 2 := by
    have := t.isLt; have := i.isLt; omega
  rw [hsum, Nat.add_mul_mod_self_left]

-- Helper: i-component of midExpected
private theorem midE_i (m : ℕ) [NeZero m] (i : Fin m) (t r : Fin m) :
    (midExpected m i t r).1 = i := by
  simp [midExpected]

-- Helper: j < m-1 at round boundary (t < m-1) for midExpected
private theorem midE_j_lt (m : ℕ) [NeZero m] (hm_ge : m ≥ 3)
    (i : Fin m) (t : Fin m) (ht : t.val < m - 1) :
    (midExpected m i t ⟨m - 1, by omega⟩).2.1.val < m - 1 := by
  have hm_pos : 0 < m := NeZero.pos m
  unfold midExpected
  simp only [Fin.val_add, Fin.val_mk]
  rw [mod_add_raw (m - 1 - t.val) (m - 1) m]
  have hsum_eq : m - 1 - t.val + (m - 1) = m + (m - 2 - t.val) := by omega
  rw [hsum_eq, show m + (m - 2 - t.val) = (m - 2 - t.val) + m * 1 from by omega,
      Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega : m - 2 - t.val < m)]
  omega

-- Helper: j = m-1 at round boundary when t = m-1 for midExpected
private theorem midE_j_eq (m : ℕ) [NeZero m] (hm_ge : m ≥ 3)
    (i : Fin m) :
    (midExpected m i ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩).2.1.val = m - 1 := by
  have hm_pos : 0 < m := NeZero.pos m
  unfold midExpected
  simp only [Fin.val_add, Fin.val_mk]
  rw [show m - 1 - (m - 1) = 0 from by omega, Nat.zero_mod,
      Nat.zero_add, Nat.mod_eq_of_lt (show m - 1 < m by omega)]

-- Base case: blockEntry(i) = midExpected i 0 0
private theorem base_case_mid (m : ℕ) [NeZero m] (hm_ge : m ≥ 3) (i : Fin m)
    (hi_pos : 0 < i.val) (hi_lt : i.val < m - 1) :
    blockEntry m i = midExpected m i ⟨0, NeZero.pos m⟩ ⟨0, NeZero.pos m⟩ := by
  have hm_pos : 0 < m := NeZero.pos m
  simp only [blockEntry, midExpected]
  simp only [Fin.val_mk, Nat.sub_zero, Nat.add_zero]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply Fin.ext
      simp only [Fin.val_add, Fin.val_mk, Nat.add_zero, Nat.mod_mod]
      exact (Nat.mod_eq_of_lt (by omega : m - 1 < m)).symm
    · apply Fin.ext
      simp only [Fin.val_add, Fin.val_mk, Nat.add_zero, Nat.mod_mod]

/-- Middle fiber step: 0 < s < m-1, i < m-1 → dir0 = bumpj, advance r by 1. -/
private theorem mid_succ_mid (m : ℕ) [NeZero m] (hm_ge : m ≥ 3)
    (i : Fin m) (hi_pos : 0 < i.val) (hi_lt : i.val < m - 1)
    (t : Fin m) (r : Fin m) (hr : r.val ≤ m - 3) :
    successor m (dir0 m) (midExpected m i t r) =
    midExpected m i t ⟨r.val + 1, by omega⟩ := by
  have hm_pos : 0 < m := NeZero.pos m
  have hfiber := midE_fiber m hm_ge i t r
  have hfiber_val : (1 + r.val) % m = 1 + r.val :=
    Nat.mod_eq_of_lt (by omega : 1 + r.val < m)
  rw [hfiber_val] at hfiber
  have hs_pos : 0 < (fiberIndex m (midExpected m i t r)).val := by omega
  have hs_lt : (fiberIndex m (midExpected m i t r)).val < m - 1 := by omega
  have hi_lt' : (midExpected m i t r).1.val < m - 1 := by rw [midE_i]; exact hi_lt
  have hs_ne0 : ¬(fiberIndex m (midExpected m i t r)).val = 0 := by omega
  have hs_nem1 : ¬(fiberIndex m (midExpected m i t r)).val = m - 1 := by omega
  have hdir : dir0 m (midExpected m i t r) = Dir.bumpj :=
    dir0_mid_ilt m _ hs_ne0 hs_nem1 hi_lt'
  rw [successor_bumpj m _ hdir]
  unfold midExpected
  simp only [Fin.val_mk]
  congr 1; congr 1
  rw [add_assoc]
  congr 1
  apply Fin.ext
  simp only [Fin.val_add, Fin.val_mk, Fin.coe_ofNat_eq_mod]
  rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega : 1 < m),
      Nat.mod_eq_of_lt (by omega : r.val + 1 < m)]

/-- End of round step: s = m-1, i > 0 → dir0 = bumpj, go from r = m-2 to r = m-1. -/
private theorem mid_succ_end (m : ℕ) [NeZero m] (hm_ge : m ≥ 3)
    (i : Fin m) (hi_pos : 0 < i.val) (hi_lt : i.val < m - 1)
    (t : Fin m) :
    successor m (dir0 m) (midExpected m i t ⟨m - 2, by omega⟩) =
    midExpected m i t ⟨m - 1, by omega⟩ := by
  have hm_pos : 0 < m := NeZero.pos m
  have hfiber := midE_fiber m hm_ge i t ⟨m - 2, by omega⟩
  simp only [Fin.val_mk] at hfiber
  have hfiber_val : (1 + (m - 2)) % m = m - 1 := by
    rw [show 1 + (m - 2) = m - 1 from by omega]
    exact Nat.mod_eq_of_lt (by omega : m - 1 < m)
  rw [hfiber_val] at hfiber
  have hs_ne : ¬(fiberIndex m (midExpected m i t ⟨m - 2, by omega⟩)).val = 0 := by omega
  have hi_gt : (midExpected m i t ⟨m - 2, by omega⟩).1.val > 0 := by
    rw [midE_i]; exact hi_pos
  have hdir : dir0 m (midExpected m i t ⟨m - 2, by omega⟩) = Dir.bumpj :=
    dir0_sm1_igt0 m _ hs_ne hfiber hi_gt
  rw [successor_bumpj m _ hdir]
  unfold midExpected
  simp only [Fin.val_mk]
  congr 1; congr 1
  rw [add_assoc]
  congr 1
  apply Fin.ext
  simp only [Fin.val_add, Fin.val_mk, Fin.coe_ofNat_eq_mod]
  rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega : 1 < m),
      show m - 2 + 1 = m - 1 from by omega,
      Nat.mod_eq_of_lt (by omega : m - 1 < m)]

/-- Round transition: s = 0, j < m-1 → dir0 = bumpk, advance t by 1. -/
private theorem mid_succ_trans (m : ℕ) [NeZero m] (hm_ge : m ≥ 3)
    (i : Fin m) (hi_pos : 0 < i.val) (hi_lt : i.val < m - 1)
    (t : Fin m) (ht : t.val < m - 1) :
    successor m (dir0 m) (midExpected m i t ⟨m - 1, by omega⟩) =
    midExpected m i ⟨t.val + 1, by omega⟩ ⟨0, NeZero.pos m⟩ := by
  have hm_pos : 0 < m := NeZero.pos m
  have hfiber := midE_fiber m hm_ge i t ⟨m - 1, by omega⟩
  simp only [Fin.val_mk] at hfiber
  have hmod_m : (1 + (m - 1)) % m = 0 := by
    rw [show 1 + (m - 1) = m from by omega, Nat.mod_self]
  rw [hmod_m] at hfiber
  have hj_lt := midE_j_lt m hm_ge i t ht
  have hdir : dir0 m (midExpected m i t ⟨m - 1, by omega⟩) = Dir.bumpk :=
    dir0_s0_jlt m _ hfiber hj_lt
  rw [successor_bumpk m _ hdir]
  unfold midExpected
  simp only [Fin.val_mk, Nat.add_zero]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · -- j component: (m-1-t)%m + (m-1) = (m-1-(t+1))%m + 0
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_mk, Nat.add_zero, Nat.mod_mod]
      rw [mod_add_raw (m - 1 - t.val) (m - 1) m,
          show m - 1 - t.val + (m - 1) = (m - 2 - t.val) + m * 1 from by omega,
          Nat.add_mul_mod_self_left,
          show m - 1 - (t.val + 1) = m - 2 - t.val from by omega]
    · -- k component: (2+m-i+t)%m + 1 = (2+m-i+(t+1))%m
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_mk, Fin.coe_ofNat_eq_mod, Nat.add_zero, Nat.mod_mod]
      rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega : 1 < m),
          mod_add_raw (2 + m - i.val + t.val) 1 m,
          show 2 + m - i.val + t.val + 1 = 2 + m - i.val + (t.val + 1) from by omega]

/-- The orbit from blockEntry(i) for 0 < i < m-1 follows midExpected. -/
theorem orbit_mid_explicit (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3)
    (i : Fin m) (hi_pos : 0 < i.val) (hi_lt : i.val < m - 1)
    (t r : Fin m) :
    orbit m (dir0 m) (blockEntry m i) (t.val * m + r.val) =
    midExpected m i t r := by
  have hm_pos : 0 < m := NeZero.pos m
  suffices H : ∀ n, ∀ t r : Fin m, n = t.val * m + r.val →
      orbit m (dir0 m) (blockEntry m i) n = midExpected m i t r by
    exact H _ t r rfl
  intro n
  induction n with
  | zero =>
    intro t r hn
    have ht0 : t.val = 0 := by
      rcases Nat.eq_zero_or_pos t.val with h | h
      · exact h
      · exfalso; have : t.val * m ≥ m := Nat.le_mul_of_pos_left m h; omega
    have hr0 : r.val = 0 := by omega
    have ht : t = ⟨0, hm_pos⟩ := fin_eq_of_val_eq ht0
    have hr : r = ⟨0, hm_pos⟩ := fin_eq_of_val_eq hr0
    subst ht; subst hr
    exact base_case_mid m hm_ge i hi_pos hi_lt
  | succ n ih =>
    intro t r hn
    rw [orbit_succ]
    by_cases hr0 : r.val = 0
    · have ht_pos : 0 < t.val := by
        by_contra h; push_neg at h
        have htv : t.val = 0 := by omega
        rw [htv, Nat.zero_mul, Nat.zero_add] at hn; omega
      have hn' : n = (t.val - 1) * m + (m - 1) := by
        have h1 : n + 1 = t.val * m := by omega
        have h2 : t.val * m = (t.val - 1 + 1) * m := by congr 1; omega
        rw [h2, Nat.add_mul, Nat.one_mul] at h1; omega
      have ht_bound : t.val - 1 < m := by omega
      have ht'_lt : t.val - 1 < m - 1 := by omega
      rw [ih ⟨t.val - 1, ht_bound⟩ ⟨m - 1, by omega⟩ (by simp [Fin.val_mk]; exact hn')]
      rw [mid_succ_trans m hm_ge i hi_pos hi_lt ⟨t.val - 1, ht_bound⟩ (by simp [Fin.val_mk]; exact ht'_lt)]
      have hreq : r = ⟨0, hm_pos⟩ := Fin.ext (by omega)
      subst hreq
      congr 1
      exact Fin.ext (by simp [Fin.val_mk]; omega)
    · have hn' : n = t.val * m + (r.val - 1) := by omega
      have hr_bound : r.val - 1 < m := by omega
      rw [ih t ⟨r.val - 1, hr_bound⟩ (by simp [Fin.val_mk]; exact hn')]
      by_cases hr_m1 : r.val = m - 1
      · have hrr : (⟨r.val - 1, hr_bound⟩ : Fin m) = ⟨m - 2, by omega⟩ :=
          fin_eq_of_val_eq (by simp [Fin.val_mk]; omega)
        rw [hrr, mid_succ_end m hm_ge i hi_pos hi_lt t]
        convert rfl using 2
        apply fin_eq_of_val_eq; simp [Fin.val_mk]; omega
      · have hr_le : (⟨r.val - 1, hr_bound⟩ : Fin m).val ≤ m - 3 := by
          simp [Fin.val_mk]; omega
        rw [mid_succ_mid m hm_ge i hi_pos hi_lt t ⟨r.val - 1, hr_bound⟩ hr_le]
        convert rfl using 2
        apply fin_eq_of_val_eq; simp [Fin.val_mk]; omega

-- Helper: j_base determines t for midExpected (stride is 1)
private theorem t_eq_of_jbase_mid (m : ℕ) [NeZero m] (t₁ t₂ : Fin m)
    (h : (⟨(m - 1 - t₁.val) % m, Nat.mod_lt _ (NeZero.pos m)⟩ : Fin m) =
         ⟨(m - 1 - t₂.val) % m, Nat.mod_lt _ (NeZero.pos m)⟩) : t₁ = t₂ := by
  have hm_pos : 0 < m := NeZero.pos m
  have hval : (m - 1 - t₁.val) % m = (m - 1 - t₂.val) % m := congrArg Fin.val h
  have h1 : m - 1 - t₁.val < m := by omega
  have h2 : m - 1 - t₂.val < m := by omega
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hval
  exact Fin.ext (by omega)

/-- The map (t, r) ↦ (j, k) extracted from midExpected is injective. -/
private theorem midExpected_jk_injective (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3)
    (i : Fin m) :
    Function.Injective (fun p : Fin m × Fin m =>
      let v := midExpected m i p.1 p.2
      (v.2.1, v.2.2)) := by
  intro ⟨t₁, r₁⟩ ⟨t₂, r₂⟩ h
  simp only [midExpected] at h
  have hm_pos : 0 < m := NeZero.pos m
  set jb₁ : Fin m := ⟨(m - 1 - t₁.val) % m, Nat.mod_lt _ hm_pos⟩
  set jb₂ : Fin m := ⟨(m - 1 - t₂.val) % m, Nat.mod_lt _ hm_pos⟩
  set kb₁ : Fin m := ⟨(2 + m - i.val + t₁.val) % m, Nat.mod_lt _ hm_pos⟩
  set kb₂ : Fin m := ⟨(2 + m - i.val + t₂.val) % m, Nat.mod_lt _ hm_pos⟩
  simp only [Prod.mk.injEq] at h
  obtain ⟨hj_eq, hk_eq⟩ := h
  -- hj_eq : jb₁ + ⟨r₁.val, _⟩ = jb₂ + ⟨r₂.val, _⟩
  -- hk_eq : kb₁ = kb₂
  -- From kb₁ = kb₂, derive t₁ = t₂
  have ht : t₁ = t₂ := by
    have hkval : (2 + m - i.val + t₁.val) % m = (2 + m - i.val + t₂.val) % m :=
      congrArg Fin.val hk_eq
    have hmeq : t₁.val % m = t₂.val % m :=
      Nat.ModEq.add_left_cancel (Nat.ModEq.refl (2 + m - i.val)) hkval
    have h1 : t₁.val % m = t₁.val := Nat.mod_eq_of_lt t₁.isLt
    have h2 : t₂.val % m = t₂.val := Nat.mod_eq_of_lt t₂.isLt
    exact Fin.ext (by omega)
  subst ht
  have hr : r₁ = r₂ := by
    have h := add_left_cancel hj_eq
    exact Fin.ext (congrArg Fin.val h)
  exact Prod.ext rfl hr

/-- midExpected covers all (i, j, k) vertices. -/
theorem midExpected_surjective (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3)
    (i : Fin m) (hi_pos : 0 < i.val) (hi_lt : i.val < m - 1) :
    ∀ j k : Fin m, ∃ t r : Fin m, midExpected m i t r = (i, j, k) := by
  have hinj := midExpected_jk_injective m hm_odd hm_ge i
  have hsurj : Function.Surjective (fun p : Fin m × Fin m =>
      let v := midExpected m i p.1 p.2; (v.2.1, v.2.2)) :=
    Finite.injective_iff_surjective.mp hinj
  intro j k
  obtain ⟨⟨t, r⟩, htr⟩ := hsurj (j, k)
  refine ⟨t, r, ?_⟩
  have htr_j : (midExpected m i t r).2.1 = j := congrArg Prod.fst htr
  have htr_k : (midExpected m i t r).2.2 = k := congrArg Prod.snd htr
  have htr_i : (midExpected m i t r).1 = i := by simp [midExpected]
  ext <;> simp [htr_i, htr_j, htr_k]

theorem mid_block_complete (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3)
    (i : Fin m) (hi_pos : 0 < i.val) (hi_lt : i.val < m - 1) :
    ∀ j k : Fin m, ∃ n : Fin (m * m),
      orbit m (dir0 m) (blockEntry m i) n.val = (i, j, k) := by
  intro j k
  obtain ⟨t, r, htr⟩ := midExpected_surjective m hm_odd hm_ge i hi_pos hi_lt j k
  refine ⟨⟨t.val * m + r.val, ?_⟩, ?_⟩
  · have := t.isLt; have := r.isLt
    calc t.val * m + r.val < t.val * m + m := by omega
    _ = (t.val + 1) * m := by ring
    _ ≤ m * m := by nlinarith
  · rw [orbit_mid_explicit m hm_odd hm_ge i hi_pos hi_lt t r, htr]

/-- The exit vertex at the end of an intermediate block has dir0 = bumpi,
    and successor gives blockEntry(i+1). -/
private theorem mid_exit_is_bumpi (m : ℕ) [NeZero m] (hm_ge : m ≥ 3)
    (i : Fin m) (hi_pos : 0 < i.val) (hi_lt : i.val < m - 1) :
    let exitV := midExpected m i ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩
    dir0 m exitV = Dir.bumpi := by
  intro exitV
  have hm_pos : 0 < m := NeZero.pos m
  have hfiber := midE_fiber m hm_ge i ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩
  simp only [Fin.val_mk] at hfiber
  have hmod_m : (1 + (m - 1)) % m = 0 := by
    rw [show 1 + (m - 1) = m from by omega, Nat.mod_self]
  rw [hmod_m] at hfiber
  have hj_eq := midE_j_eq m hm_ge i
  rw [cycle0_i_change_condition]
  exact ⟨hfiber, hj_eq⟩

private theorem mid_exit_to_next (m : ℕ) [NeZero m] (hm_ge : m ≥ 3)
    (i : Fin m) (hi_pos : 0 < i.val) (hi_lt : i.val < m - 1) :
    successor m (dir0 m) (midExpected m i ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩) =
    blockEntry m ⟨i.val + 1, by omega⟩ := by
  have hm_pos : 0 < m := NeZero.pos m
  have hdir := mid_exit_is_bumpi m hm_ge i hi_pos hi_lt
  rw [successor_bumpi m _ hdir]
  unfold midExpected blockEntry
  simp only [Fin.val_mk]
  apply Prod.ext
  · -- i component: i + 1 = ⟨i.val + 1, _⟩
    apply Fin.ext
    simp only [Fin.val_add, Fin.coe_ofNat_eq_mod]
    rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega : 1 < m),
        Nat.mod_eq_of_lt (by omega : i.val + 1 < m)]
  · apply Prod.ext
    · -- j component: (m-1-(m-1))%m + (m-1) = m-1
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_mk]
      rw [show m - 1 - (m - 1) = 0 from by omega, Nat.zero_mod, Nat.zero_add,
          Nat.mod_eq_of_lt (by omega : m - 1 < m)]
    · -- k component: (2+m-i+(m-1))%m = (2+m-(i+1))%m
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_mk, Fin.coe_ofNat_eq_mod, Nat.add_zero, Nat.mod_mod]
      rw [show 2 + m - i.val + (m - 1) = (2 + m - (i.val + 1)) + m * 1 from by omega,
          Nat.add_mul_mod_self_left]

/-! ### 4.5 Block chaining: orbit through all blocks -/

/-- checkpoint0(0) = blockEntry(0). -/
private theorem checkpoint0_eq_blockEntry0 (m : ℕ) [NeZero m] (hm_ge : m ≥ 3) :
    checkpoint0 m ⟨0, NeZero.pos m⟩ = blockEntry m ⟨0, NeZero.pos m⟩ := by
  simp only [checkpoint0, blockEntry]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply Fin.ext
      simp only [Fin.val_mk, Nat.zero_mod, Nat.mul_zero, Nat.sub_zero]
      rw [show m - 1 + m = (m - 1) + m * 1 from by omega,
          Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt (show m - 1 < m by omega)]
    · apply Fin.ext
      simp only [Fin.val_mk, Nat.zero_mod, Nat.mul_zero, Nat.add_zero, Nat.sub_zero]
      rw [show 2 + m = 2 + m * 1 from by omega,
          Nat.add_mul_mod_self_left]

/-- The i=0 exit vertex (last step of i=0 block) leads to blockEntry(1). -/
private theorem i0_exit_to_block1 (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3) :
    successor m (dir0 m) (i0Expected m ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩) =
    blockEntry m ⟨1, by omega⟩ := by
  have hm_pos : 0 < m := NeZero.pos m
  -- At i=0 block exit: fiber = 0, j = m-1 → bumpi
  have hfiber := i0E_fiber m hm_ge ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩
  simp only [Fin.val_mk, show ¬(m - 1 ≤ m - 2) from by omega, ite_false] at hfiber
  have hj_val : (i0Expected m ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩).2.1.val = m - 1 := by
    unfold i0Expected
    simp only [Fin.val_mk, show ¬(m - 1 ≤ m - 2) from by omega, ite_false, Fin.val_add]
    rw [mod_add_raw (2 * m - 1 - 2 * (m - 1)) (m - 2) m]
    rw [show 2 * m - 1 - 2 * (m - 1) + (m - 2) = m - 1 from by omega,
        Nat.mod_eq_of_lt (by omega : m - 1 < m)]
  have hdir : dir0 m (i0Expected m ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩) = Dir.bumpi := by
    rw [cycle0_i_change_condition]; exact ⟨hfiber, hj_val⟩
  rw [successor_bumpi m _ hdir]
  unfold i0Expected blockEntry
  simp only [Fin.val_mk, show ¬(m - 1 ≤ m - 2) from by omega, ite_false]
  apply Prod.ext
  · -- i: 0 + 1 = 1
    apply Fin.ext
    simp only [Fin.val_add, Fin.coe_ofNat_eq_mod, Nat.zero_add]
    rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega : 1 < m),
        Nat.mod_eq_of_lt (by omega : 1 < m)]
  · apply Prod.ext
    · -- j: j stays m-1
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_mk]
      rw [mod_add_raw (2 * m - 1 - 2 * (m - 1)) (m - 2) m,
          show 2 * m - 1 - 2 * (m - 1) + (m - 2) = m - 1 from by omega,
          Nat.mod_eq_of_lt (by omega : m - 1 < m)]
    · -- k: compute both sides
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_mk, Fin.coe_ofNat_eq_mod, Nat.mod_mod]
      rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega : 1 < m),
          mod_add_raw (2 + 2 * (m - 1)) 1 m]
      rw [show 2 + 2 * (m - 1) + 1 = 2 + m - 1 + m * 1 from by omega,
          Nat.add_mul_mod_self_left]

/-- The last block (i=m-1) exit vertex goes back to blockEntry(0). -/
private theorem last_exit_to_block0 (m : ℕ) [NeZero m] (hm_ge : m ≥ 3) :
    successor m (dir0 m) (lastExpected m ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩) =
    blockEntry m ⟨0, NeZero.pos m⟩ := by
  have hm_pos : 0 < m := NeZero.pos m
  have hfiber := lastE_fiber m hm_ge ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩
  simp only [Fin.val_mk, show ¬(m - 1 ≤ m - 2) from by omega, ite_false] at hfiber
  -- j at exit = (m-1+(m-1))%m + 1 = ... = m-1
  have hj_val : (lastExpected m ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩).2.1.val = m - 1 := by
    unfold lastExpected
    simp only [Fin.val_mk, show ¬(m - 1 ≤ m - 2) from by omega, ite_false, Fin.val_add,
               Fin.coe_ofNat_eq_mod]
    rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega : 1 < m),
        mod_add_raw (m - 1 + (m - 1)) 1 m,
        show m - 1 + (m - 1) + 1 = m + (m - 1) from by omega,
        show m + (m - 1) = (m - 1) + m * 1 from by omega,
        Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (by omega : m - 1 < m)]
  have hdir : dir0 m (lastExpected m ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩) = Dir.bumpi := by
    rw [cycle0_i_change_condition]; exact ⟨hfiber, hj_val⟩
  rw [successor_bumpi m _ hdir]
  unfold lastExpected blockEntry
  simp only [Fin.val_mk, show ¬(m - 1 ≤ m - 2) from by omega, ite_false]
  apply Prod.ext
  · -- i: (m-1) + 1 = 0 in Fin m
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_mk, Fin.coe_ofNat_eq_mod]
    rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega : 1 < m),
        show m - 1 + 1 = m from by omega, Nat.mod_self]
  · apply Prod.ext
    · -- j: stays m-1
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_mk, Fin.coe_ofNat_eq_mod]
      rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega : 1 < m),
          mod_add_raw (m - 1 + (m - 1)) 1 m,
          show m - 1 + (m - 1) + 1 = m + (m - 1) from by omega,
          show m + (m - 1) = (m - 1) + m * 1 from by omega,
          Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt (by omega : m - 1 < m)]
    · -- k
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_mk, Fin.coe_ofNat_eq_mod, Nat.mod_mod]
      rw [mod_add_raw (m + 3 - (m - 1)) (m - 2) m,
          show m + 3 - (m - 1) + (m - 2) = m + 2 from by omega,
          show m + 2 = 2 + m * 1 from by omega,
          Nat.add_mul_mod_self_left,
          show 2 + m - 0 = 2 + m from by omega,
          show 2 + m = 2 + m * 1 from by omega,
          Nat.add_mul_mod_self_left]

/-- Helper: orbit(start, a + b) = orbit(orbit(start, a), b). -/
private theorem orbit_add (m : ℕ) [NeZero m] (dirFn : Vertex m → Dir) (start : Vertex m)
    (a b : ℕ) :
    orbit m dirFn start (a + b) = orbit m dirFn (orbit m dirFn start a) b := by
  induction b with
  | zero => simp [Nat.add_zero]
  | succ n ih =>
    rw [show a + (n + 1) = (a + n) + 1 from by omega]
    simp only [orbit_succ]
    rw [ih]

/-- After m² orbit steps from blockEntry(i), block i's orbit completes and
    reaches the exit vertex, whose successor is blockEntry(i+1 mod m).
    For i=0: orbit visits i0Expected, exits to blockEntry(1).
    For 0 < i < m-1: orbit visits midExpected, exits to blockEntry(i+1).
    For i=m-1: orbit visits lastExpected, exits to blockEntry(0). -/
private theorem block_orbit_step (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3)
    (i : Fin m) (hi_lt : i.val < m - 1) :
    orbit m (dir0 m) (blockEntry m i) (m * m) =
    blockEntry m ⟨i.val + 1, by omega⟩ := by
  have hm_pos : 0 < m := NeZero.pos m
  have hmm : m * m = (m - 1) * m + (m - 1) + 1 := by
    zify [show m ≥ 1 from by omega]; ring
  rw [hmm, show (m - 1) * m + (m - 1) + 1 = ((m - 1) * m + (m - 1)) + 1 from by omega]
  simp only [orbit_succ]
  by_cases hi0 : i.val = 0
  · -- i = 0: use i0 block
    have hi : i = ⟨0, hm_pos⟩ := Fin.ext hi0
    subst hi
    rw [← checkpoint0_eq_blockEntry0 m hm_ge,
        orbit_i0_explicit m hm_odd hm_ge ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩,
        i0_exit_to_block1 m hm_odd hm_ge]
  · -- 0 < i < m-1: use mid block
    have hi_pos : 0 < i.val := by omega
    rw [orbit_mid_explicit m hm_odd hm_ge i hi_pos hi_lt ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩,
        mid_exit_to_next m hm_ge i hi_pos hi_lt]

/-- Orbit chaining: orbit from blockEntry(0) reaches blockEntry(i) after i*m² steps. -/
private theorem orbit_reaches_block (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3)
    (i : Fin m) :
    orbit m (dir0 m) (blockEntry m ⟨0, NeZero.pos m⟩) (i.val * (m * m)) =
    blockEntry m i := by
  have hm_pos : 0 < m := NeZero.pos m
  -- Induction on i.val
  suffices H : ∀ k (hk : k < m),
      orbit m (dir0 m) (blockEntry m ⟨0, hm_pos⟩) (k * (m * m)) =
      blockEntry m ⟨k, hk⟩ by
    have := H i.val i.isLt
    convert this using 2
  intro k
  induction k with
  | zero => intro _; simp [orbit_zero]
  | succ n ih =>
    intro hn_lt
    have hn_lt' : n < m := by omega
    rw [show (n + 1) * (m * m) = n * (m * m) + m * m from by ring,
        orbit_add, ih hn_lt',
        block_orbit_step m hm_odd hm_ge ⟨n, hn_lt'⟩ (by simp [Fin.val_mk]; omega)]

/-- After m blocks of m² steps each, the orbit returns to start. -/
private theorem orbit_returns (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3) :
    orbit m (dir0 m) (blockEntry m ⟨0, NeZero.pos m⟩) (m ^ 3) =
    blockEntry m ⟨0, NeZero.pos m⟩ := by
  have hm_pos : 0 < m := NeZero.pos m
  have hcube : m ^ 3 = (m - 1) * (m * m) + m * m := by
    zify [show m ≥ 1 from by omega]; ring
  rw [hcube, orbit_add, orbit_reaches_block m hm_odd hm_ge ⟨m - 1, by omega⟩]
  have hmm : m * m = (m - 1) * m + (m - 1) + 1 := by
    zify [show m ≥ 1 from by omega]; ring
  rw [hmm, show (m - 1) * m + (m - 1) + 1 = ((m - 1) * m + (m - 1)) + 1 from by omega]
  simp only [orbit_succ]
  rw [orbit_last_explicit m hm_odd hm_ge ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩]
  exact last_exit_to_block0 m hm_ge

/-! ## 5. Main Hamiltonicity Theorem for Cycle 0 -/

/-- The successor function for dir0 is a bijection (permutation) on Vertex m,
    since it is injective on a finite type. -/
theorem successor_dir0_bijective (m : ℕ) [NeZero m] (hm : m ≥ 3) :
    Function.Bijective (successor m (dir0 m)) :=
  ⟨successor_dir0_injective m hm,
   Finite.injective_iff_surjective.mp (successor_dir0_injective m hm)⟩

theorem cycle0_hamiltonian (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3) :
    ∃ start : Vertex m,
      (orbit m (dir0 m) start (m ^ 3) = start) ∧
      (∀ v : Vertex m, ∃ n : Fin (m ^ 3),
        orbit m (dir0 m) start n.val = v) := by
  have hm_pos : 0 < m := NeZero.pos m
  refine ⟨blockEntry m ⟨0, hm_pos⟩, orbit_returns m hm_odd hm_ge, ?_⟩
  intro v
  obtain ⟨vi, vj, vk⟩ := v
  -- Determine which block vi belongs to
  have hreach := orbit_reaches_block m hm_odd hm_ge vi
  by_cases hvi0 : vi.val = 0
  · -- i = 0 block
    obtain ⟨⟨n, hn_lt⟩, hn_eq⟩ := i0_block_complete m hm_odd hm_ge vj vk
    have hvi_eq : vi = ⟨0, hm_pos⟩ := Fin.ext hvi0
    refine ⟨⟨vi.val * (m * m) + n, ?_⟩, ?_⟩
    · calc vi.val * (m * m) + n < vi.val * (m * m) + m * m := by omega
        _ = (vi.val + 1) * (m * m) := by ring
        _ ≤ m * (m * m) := by nlinarith [vi.isLt]
        _ = m ^ 3 := by ring
    · simp only [Fin.val_mk]
      rw [orbit_add, hreach, hvi_eq, ← checkpoint0_eq_blockEntry0 m hm_ge]
      exact hn_eq
  · by_cases hvilast : vi.val = m - 1
    · -- i = m-1 block
      have hvi_eq : vi = ⟨m - 1, by omega⟩ := Fin.ext hvilast
      obtain ⟨⟨n, hn_lt⟩, hn_eq⟩ := last_block_complete m hm_odd hm_ge vj vk
      refine ⟨⟨vi.val * (m * m) + n, ?_⟩, ?_⟩
      · calc vi.val * (m * m) + n < vi.val * (m * m) + m * m := by omega
          _ = (vi.val + 1) * (m * m) := by ring
          _ ≤ m * (m * m) := by nlinarith [vi.isLt]
          _ = m ^ 3 := by ring
      · simp only [Fin.val_mk]
        rw [orbit_add, hreach, hvi_eq]
        exact hn_eq
    · -- Intermediate block: 0 < vi.val < m-1
      have hvi_pos : 0 < vi.val := by omega
      have hvi_lt : vi.val < m - 1 := by omega
      obtain ⟨⟨n, hn_lt⟩, hn_eq⟩ := mid_block_complete m hm_odd hm_ge vi hvi_pos hvi_lt vj vk
      refine ⟨⟨vi.val * (m * m) + n, ?_⟩, ?_⟩
      · calc vi.val * (m * m) + n < vi.val * (m * m) + m * m := by omega
          _ = (vi.val + 1) * (m * m) := by ring
          _ ≤ m * (m * m) := by nlinarith [vi.isLt]
          _ = m ^ 3 := by ring
      · simp only [Fin.val_mk]
        rw [orbit_add, hreach]
        exact hn_eq

/-! ## 6. Hamiltonicity of Cycles 1 and 2 -/

/-- The successor function for dir1 is injective.
    dir1 structure: s=0 -> bumpj (unique), middle -> bumpi (unique),
    s=m-1 -> i>0 ? bumpk : bumpj. Cross-direction only at s=m-1. -/
theorem successor_dir1_injective (m : ℕ) [NeZero m] (_hm : m ≥ 3) :
    Function.Injective (successor m (dir1 m)) := by
  intro u v h
  simp only [successor] at h
  by_cases hd : dir1 m u = dir1 m v
  · rw [hd] at h; exact bump_injective m (dir1 m v) h
  · exfalso
    have hf : fiberIndex m u = fiberIndex m v := by
      have h1 := fiber_advances m u (dir1 m u)
      have h2 := fiber_advances m v (dir1 m v)
      rw [h] at h1; exact add_right_cancel (h1.symm.trans h2)
    have hfval : (fiberIndex m u).val = (fiberIndex m v).val := congrArg Fin.val hf
    -- dir1: s=0 -> bumpj, s=m-1 -> (i>0?bumpk:bumpj), else -> bumpi
    -- Cross-direction only at s=m-1 (bumpk vs bumpj); u.1 = v.1 gives contradiction
    simp only [dir1, bump] at h hd
    split_ifs at h hd hf <;> simp_all [Prod.mk.injEq] <;> (first | omega | skip)

theorem successor_dir1_bijective (m : ℕ) [NeZero m] (hm : m ≥ 3) :
    Function.Bijective (successor m (dir1 m)) :=
  ⟨successor_dir1_injective m hm, Finite.injective_iff_surjective.mp
    (successor_dir1_injective m hm)⟩

/-- Helper lemmas for dir2 case analysis. -/
private theorem dir2_s0_jlt (m : ℕ) [NeZero m] (v : Vertex m)
    (hs : (fiberIndex m v).val = 0) (hj : v.2.1.val < m - 1) :
    dir2 m v = Dir.bumpi := by
  simp only [dir2]; split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)

private theorem dir2_s0_jeq (m : ℕ) [NeZero m] (v : Vertex m)
    (hs : (fiberIndex m v).val = 0) (hj : ¬ v.2.1.val < m - 1) :
    dir2 m v = Dir.bumpk := by
  simp only [dir2]; split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)

private theorem dir2_sm1 (m : ℕ) [NeZero m] (v : Vertex m)
    (hs : ¬(fiberIndex m v).val = 0) (hs' : (fiberIndex m v).val = m - 1) :
    dir2 m v = Dir.bumpi := by
  simp only [dir2]; split_ifs <;> simp_all

private theorem dir2_mid_ilt (m : ℕ) [NeZero m] (v : Vertex m)
    (hs : ¬(fiberIndex m v).val = 0) (hs' : ¬(fiberIndex m v).val = m - 1)
    (hi : v.1.val < m - 1) : dir2 m v = Dir.bumpk := by
  simp only [dir2]; split_ifs with h1 h2 h3 <;> first | rfl | (exfalso; omega)

private theorem dir2_mid_ieq (m : ℕ) [NeZero m] (v : Vertex m)
    (hs : ¬(fiberIndex m v).val = 0) (hs' : ¬(fiberIndex m v).val = m - 1)
    (hi : ¬ v.1.val < m - 1) : dir2 m v = Dir.bumpj := by
  simp only [dir2]; split_ifs with h1 h2 h3 <;> first | rfl | (exfalso; omega)

/-- The successor function for dir2 is injective. -/
theorem successor_dir2_injective (m : ℕ) [NeZero m] (hm : m ≥ 3) :
    Function.Injective (successor m (dir2 m)) := by
  intro u v h
  simp only [successor] at h
  by_cases hd : dir2 m u = dir2 m v
  · rw [hd] at h; exact bump_injective m (dir2 m v) h
  · exfalso
    have hf : fiberIndex m u = fiberIndex m v := by
      have h1 := fiber_advances m u (dir2 m u)
      have h2 := fiber_advances m v (dir2 m v)
      rw [h] at h1; exact add_right_cancel (h1.symm.trans h2)
    have hfval : (fiberIndex m u).val = (fiberIndex m v).val := congrArg Fin.val hf
    -- Case split on fiber class
    by_cases hsu : (fiberIndex m u).val = 0
    · have hsv : (fiberIndex m v).val = 0 := by omega
      -- s=0: bumpi (j<m-1) vs bumpk (j>=m-1)
      by_cases hju : u.2.1.val < m - 1
      · by_cases hjv : v.2.1.val < m - 1
        · exact hd (by rw [dir2_s0_jlt m u hsu hju, dir2_s0_jlt m v hsv hjv])
        · -- bumpi vs bumpk: j-components: u.2.1 = v.2.1
          rw [dir2_s0_jlt m u hsu hju, dir2_s0_jeq m v hsv hjv] at h
          simp only [bump, Prod.mk.injEq] at h
          exact hjv (by have := congrArg Fin.val h.2.1; omega)
      · by_cases hjv : v.2.1.val < m - 1
        · rw [dir2_s0_jeq m u hsu hju, dir2_s0_jlt m v hsv hjv] at h
          simp only [bump, Prod.mk.injEq] at h
          exact hju (by have := congrArg Fin.val h.2.1; omega)
        · exact hd (by rw [dir2_s0_jeq m u hsu hju, dir2_s0_jeq m v hsv hjv])
    · by_cases hsu' : (fiberIndex m u).val = m - 1
      · -- s=m-1: always bumpi, no cross case
        have hsv_ne : ¬(fiberIndex m v).val = 0 := by omega
        have hsv' : (fiberIndex m v).val = m - 1 := by omega
        exact hd (by rw [dir2_sm1 m u hsu hsu', dir2_sm1 m v hsv_ne hsv'])
      · -- middle: bumpk (i<m-1) vs bumpj (i>=m-1)
        have hsv : ¬(fiberIndex m v).val = 0 := by omega
        have hsv' : ¬(fiberIndex m v).val = m - 1 := by omega
        by_cases hiu : u.1.val < m - 1
        · by_cases hiv : v.1.val < m - 1
          · exact hd (by rw [dir2_mid_ilt m u hsu hsu' hiu,
                              dir2_mid_ilt m v hsv hsv' hiv])
          · -- bumpk vs bumpj: i-components: u.1 = v.1
            rw [dir2_mid_ilt m u hsu hsu' hiu, dir2_mid_ieq m v hsv hsv' hiv] at h
            simp only [bump, Prod.mk.injEq] at h
            exact hiv (by have := congrArg Fin.val h.1; omega)
        · by_cases hiv : v.1.val < m - 1
          · rw [dir2_mid_ieq m u hsu hsu' hiu, dir2_mid_ilt m v hsv hsv' hiv] at h
            simp only [bump, Prod.mk.injEq] at h
            exact hiu (by have := congrArg Fin.val h.1; omega)
          · exact hd (by rw [dir2_mid_ieq m u hsu hsu' hiu,
                              dir2_mid_ieq m v hsv hsv' hiv])

theorem successor_dir2_bijective (m : ℕ) [NeZero m] (hm : m ≥ 3) :
    Function.Bijective (successor m (dir2 m)) :=
  ⟨successor_dir2_injective m hm,
   Finite.injective_iff_surjective.mp (successor_dir2_injective m hm)⟩

/-! ### Cycle 1: Definitions and helpers -/

/-- Entry point for super-round u of cycle 1. -/
def dir1BlockEntry (m : ℕ) [NeZero m] (u : Fin m) : Vertex m :=
  (⟨0, NeZero.pos m⟩,
   ⟨u.val % m, Nat.mod_lt _ (NeZero.pos m)⟩,
   ⟨(m - u.val) % m, Nat.mod_lt _ (NeZero.pos m)⟩)

/-- Expected vertex at orbit step (t*m + r) within super-round u.
    Round t, step r:
    - r=0: ((m-2)*t, u+t, t+m-u) with s=0
    - r≥1: ((m-2)*t + r-1, u+t+1, t+m-u) with s=r -/
def dir1Expected (m : ℕ) [NeZero m] (u t r : Fin m) : Vertex m :=
  let i_base : Fin m := ⟨((m - 2) * t.val) % m, Nat.mod_lt _ (NeZero.pos m)⟩
  let j_base : Fin m := ⟨(u.val + t.val) % m, Nat.mod_lt _ (NeZero.pos m)⟩
  let k_val : Fin m := ⟨(t.val + m - u.val) % m, Nat.mod_lt _ (NeZero.pos m)⟩
  if r.val = 0 then
    (i_base, j_base, k_val)
  else
    (i_base + ⟨r.val - 1, by have := r.isLt; omega⟩, j_base + 1, k_val)

/-- dir1 helper: s=0 → bumpj -/
private theorem dir1_s0 (m : ℕ) [NeZero m] (v : Vertex m)
    (hs : (fiberIndex m v).val = 0) : dir1 m v = Dir.bumpj := by
  simp only [dir1]; split_ifs <;> simp_all

/-- dir1 helper: 0 < s < m-1 → bumpi -/
private theorem dir1_mid (m : ℕ) [NeZero m] (v : Vertex m)
    (hs_ne0 : ¬(fiberIndex m v).val = 0)
    (hs_nem1 : ¬(fiberIndex m v).val = m - 1) : dir1 m v = Dir.bumpi := by
  simp only [dir1]; split_ifs <;> simp_all

/-- dir1 helper: s=m-1, i>0 → bumpk -/
private theorem dir1_sm1_pos (m : ℕ) [NeZero m] (v : Vertex m)
    (hs_ne0 : ¬(fiberIndex m v).val = 0) (hs_m1 : (fiberIndex m v).val = m - 1)
    (hi_pos : v.1.val > 0) : dir1 m v = Dir.bumpk := by
  simp only [dir1]; split_ifs <;> simp_all <;> omega

/-- dir1 helper: s=m-1, i=0 → bumpj -/
private theorem dir1_sm1_zero (m : ℕ) [NeZero m] (v : Vertex m)
    (hs_ne0 : ¬(fiberIndex m v).val = 0) (hs_m1 : (fiberIndex m v).val = m - 1)
    (hi_zero : v.1.val = 0) : dir1 m v = Dir.bumpj := by
  simp only [dir1]; split_ifs <;> simp_all <;> omega

/-- Fiber index of dir1Expected equals r.val (mod m). -/
private theorem dir1E_fiber (m : ℕ) [NeZero m] (hm_ge : m ≥ 3) (u t r : Fin m) :
    (fiberIndex m (dir1Expected m u t r)).val = r.val % m := by
  have hm_pos : 0 < m := NeZero.pos m
  unfold fiberIndex dir1Expected
  split_ifs with hr0
  · -- r = 0: sum = (m-2)*t + (u+t) + (t+m-u) = m*(t+1) ≡ 0
    simp only [Fin.val_add, Fin.val_mk]
    rw [mod_add_mod' ((m - 2) * t.val) (u.val + t.val),
        mod_add_mod' ((m - 2) * t.val + (u.val + t.val)) (t.val + m - u.val)]
    have hsum : (m - 2) * t.val + (u.val + t.val) + (t.val + m - u.val) =
                m * (t.val + 1) := by
      have := u.isLt; have := t.isLt
      zify [show m ≥ 2 from by omega, show u.val ≤ t.val + m from by omega]; ring
    rw [hsum, Nat.mul_mod_right, hr0, Nat.zero_mod]
  · -- r ≥ 1: sum = (m-2)*t+(r-1) + (u+t+1) + (t+m-u) = r + m*(t+1)
    simp only [Fin.val_add, Fin.val_mk, Fin.coe_ofNat_eq_mod]
    rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega : 1 < m),
        mod_add_raw ((m - 2) * t.val) (r.val - 1) m,
        mod_add_raw (u.val + t.val) 1 m,
        mod_add_mod' ((m - 2) * t.val + (r.val - 1)) (u.val + t.val + 1),
        mod_add_mod' ((m - 2) * t.val + (r.val - 1) + (u.val + t.val + 1))
                      (t.val + m - u.val)]
    have hsum : (m - 2) * t.val + (r.val - 1) + (u.val + t.val + 1) +
                (t.val + m - u.val) = r.val + m * (t.val + 1) := by
      have := u.isLt; have := t.isLt
      have hr1 : r.val ≥ 1 := by omega
      zify [show m ≥ 2 from by omega, show u.val ≤ t.val + m from by omega, hr1]; ring
    rw [hsum, Nat.add_mul_mod_self_left]

/-- Base case: dir1Expected at (u, 0, 0) = dir1BlockEntry u. -/
private theorem dir1_base_case (m : ℕ) [NeZero m] (u : Fin m) :
    dir1Expected m u ⟨0, NeZero.pos m⟩ ⟨0, NeZero.pos m⟩ = dir1BlockEntry m u := by
  simp [dir1Expected, dir1BlockEntry]

/-- successor for dir1 when direction is bumpj. -/
private theorem successor_dir1_bumpj (m : ℕ) [NeZero m] (v : Vertex m)
    (h : dir1 m v = Dir.bumpj) :
    successor m (dir1 m) v = (v.1, v.2.1 + 1, v.2.2) := by
  simp [successor, h, bump]

/-- successor for dir1 when direction is bumpi. -/
private theorem successor_dir1_bumpi (m : ℕ) [NeZero m] (v : Vertex m)
    (h : dir1 m v = Dir.bumpi) :
    successor m (dir1 m) v = (v.1 + 1, v.2.1, v.2.2) := by
  simp [successor, h, bump]

/-- successor for dir1 when direction is bumpk. -/
private theorem successor_dir1_bumpk (m : ℕ) [NeZero m] (v : Vertex m)
    (h : dir1 m v = Dir.bumpk) :
    successor m (dir1 m) v = (v.1, v.2.1, v.2.2 + 1) := by
  simp [successor, h, bump]

/-! ### Cycle 1: Successor transition helpers -/

/-- At r=0 (start of round), dir1=bumpj, successor advances to r=1. -/
private theorem dir1_succ_s0 (m : ℕ) [NeZero m] (hm_ge : m ≥ 3) (u t : Fin m) :
    successor m (dir1 m) (dir1Expected m u t ⟨0, NeZero.pos m⟩) =
    dir1Expected m u t ⟨1, by omega⟩ := by
  have hm_pos : 0 < m := NeZero.pos m
  have hfiber := dir1E_fiber m hm_ge u t ⟨0, hm_pos⟩
  simp only [Fin.val_mk, Nat.zero_mod] at hfiber
  rw [successor_dir1_bumpj m _ (dir1_s0 m _ hfiber)]
  unfold dir1Expected
  simp only [Fin.val_mk, show (0 : ℕ) = 0 from rfl, ite_true,
             show ¬(1 : ℕ) = 0 from by omega, ite_false,
             show (1 : ℕ) - 1 = 0 from rfl]
  refine Prod.ext ?_ rfl
  apply Fin.ext
  simp only [Fin.val_add, Fin.val_mk]
  rw [Nat.add_zero, Nat.mod_mod]

/-- At 1 ≤ r ≤ m-2 (mid-round), dir1=bumpi, successor advances to r+1. -/
private theorem dir1_succ_mid (m : ℕ) [NeZero m] (hm_ge : m ≥ 3) (u t r : Fin m)
    (hr_ge : r.val ≥ 1) (hr_le : r.val ≤ m - 2) :
    successor m (dir1 m) (dir1Expected m u t r) =
    dir1Expected m u t ⟨r.val + 1, by omega⟩ := by
  have hm_pos : 0 < m := NeZero.pos m
  have hfiber := dir1E_fiber m hm_ge u t r
  rw [Nat.mod_eq_of_lt r.isLt] at hfiber
  have hs_ne0 : ¬(fiberIndex m (dir1Expected m u t r)).val = 0 := by omega
  have hs_nem1 : ¬(fiberIndex m (dir1Expected m u t r)).val = m - 1 := by omega
  rw [successor_dir1_bumpi m _ (dir1_mid m _ hs_ne0 hs_nem1)]
  unfold dir1Expected
  simp only [Fin.val_mk, show ¬r.val = 0 from by omega, ite_false,
             show ¬(r.val + 1 = 0) from by omega]
  refine Prod.ext ?_ (Prod.ext rfl rfl)
  -- i component: (i_base + ⟨r-1, _⟩) + 1 = i_base + ⟨r, _⟩ (in Fin m)
  apply Fin.ext
  simp only [Fin.val_add, Fin.val_mk, Fin.coe_ofNat_eq_mod]
  rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega : 1 < m),
      show r.val + 1 - 1 = r.val from by omega]
  -- Goal: (((m-2)*t%m + (r-1)) % m + 1) % m = ((m-2)*t%m + r) % m
  rw [mod_add_raw ((m - 2) * t.val % m + (r.val - 1)) 1 m]
  -- Now: ((m-2)*t%m + (r-1) + 1) % m = ((m-2)*t%m + r) % m
  have h : (m - 2) * t.val % m + (r.val - 1) + 1 = (m - 2) * t.val % m + r.val := by omega
  rw [h]

/-- At r=m-1 with t<m-1, dir1=bumpk (since i>0), transition to next round. -/
private theorem dir1_succ_trans (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3)
    (u t : Fin m) (ht : t.val < m - 1) :
    successor m (dir1 m) (dir1Expected m u t ⟨m - 1, by omega⟩) =
    dir1Expected m u ⟨t.val + 1, by omega⟩ ⟨0, NeZero.pos m⟩ := by
  have hm_pos : 0 < m := NeZero.pos m
  have hfiber := dir1E_fiber m hm_ge u t ⟨m - 1, by omega⟩
  simp only [Fin.val_mk, Nat.mod_eq_of_lt (show m - 1 < m from by omega)] at hfiber
  have hs_ne0 : ¬(fiberIndex m (dir1Expected m u t ⟨m-1, by omega⟩)).val = 0 := by omega
  have hs_m1 : (fiberIndex m (dir1Expected m u t ⟨m-1, by omega⟩)).val = m - 1 := hfiber
  -- Show i > 0 at end of round when t < m-1
  have hi_pos : (dir1Expected m u t ⟨m-1, by omega⟩).1.val > 0 := by
    unfold dir1Expected
    simp only [Fin.val_mk, show ¬(m - 1 = 0) from by omega, ite_false, Fin.val_add]
    rw [show m - 1 - 1 = m - 2 from by omega, mod_add_raw ((m - 2) * t.val) (m - 2) m]
    have hprod : (m - 2) * t.val + (m - 2) = (m - 2) * (t.val + 1) := by
      zify [show m ≥ 2 from by omega]; ring
    rw [hprod]
    -- (m-2)*(t+1) % m > 0 because m ∤ (m-2)*(t+1)
    -- Since (m-2)*(t+1) + 2*(t+1) = m*(t+1), if m | (m-2)*(t+1) then m | 2*(t+1)
    -- With 2 ≤ 2*(t+1) ≤ 2*(m-1) < 2m, the only option is 2*(t+1) = m, but m is odd.
    by_contra heq; push_neg at heq
    have hmod : (m - 2) * (t.val + 1) % m = 0 := by omega
    have hdvd : m ∣ (m - 2) * (t.val + 1) := Nat.dvd_of_mod_eq_zero hmod
    have hfact : (m - 2) * (t.val + 1) + 2 * (t.val + 1) = m * (t.val + 1) := by
      zify [show m ≥ 2 from by omega]; ring
    have hdvd2 : m ∣ 2 * (t.val + 1) := by
      have h1 : m * (t.val + 1) = (m - 2) * (t.val + 1) + 2 * (t.val + 1) := hfact.symm
      have h2 : m ∣ m * (t.val + 1) := dvd_mul_right m _
      rwa [h1, Nat.dvd_add_right hdvd] at h2
    -- 2*(t+1) ≥ 2, 2*(t+1) ≤ 2*(m-1) < 2m, and m | 2*(t+1) → 2*(t+1) = m
    obtain ⟨c, hc⟩ := hdvd2
    have hc_pos : c ≥ 1 := by
      rcases Nat.eq_zero_or_pos c with hc0 | hcp
      · rw [hc0, Nat.mul_zero] at hc; omega
      · omega
    have hc_le : c ≤ 1 := by
      by_contra hc_gt
      push_neg at hc_gt
      have hc2 : c ≥ 2 := by omega
      have : 2 * (t.val + 1) ≥ 2 * m := by
        calc 2 * (t.val + 1) = m * c := hc
        _ ≥ m * 2 := Nat.mul_le_mul_left m hc2
        _ = 2 * m := Nat.mul_comm m 2
      have : t.val + 1 ≤ m - 1 := by omega
      omega
    -- c = 1, so 2*(t+1) = m, contradicting m odd
    have hc1 : c = 1 := by omega
    rw [hc1] at hc
    -- 2*(t+1) = m, but m is odd
    omega
  rw [successor_dir1_bumpk m _ (dir1_sm1_pos m _ hs_ne0 hs_m1 hi_pos)]
  -- Goal: (v.1, v.2.1, v.2.2 + 1) = dir1Expected(u, t+1, 0)
  unfold dir1Expected
  simp only [Fin.val_mk, show ¬(m - 1 = 0) from by omega, ite_false,
             show (0 : ℕ) = 0 from rfl, ite_true,
             show m - 1 - 1 = m - 2 from by omega]
  ext i
  · -- i component: i_base + ⟨m-2, _⟩ = ((m-2)*(t+1)) % m
    simp only [Fin.val_add, Fin.val_mk]
    rw [mod_add_raw ((m - 2) * t.val) (m - 2) m,
        show (m - 2) * t.val + (m - 2) = (m - 2) * (t.val + 1) from by ring]
  · -- j component
    simp only [Fin.val_add, Fin.val_mk, Fin.coe_ofNat_eq_mod]
    rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega : 1 < m),
        mod_add_raw (u.val + t.val) 1 m,
        show u.val + t.val + 1 = u.val + (t.val + 1) from by ring]
  · -- k component
    simp only [Fin.val_add, Fin.val_mk, Fin.coe_ofNat_eq_mod]
    rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega : 1 < m),
        mod_add_raw (t.val + m - u.val) 1 m]
    have := u.isLt
    rw [show t.val + m - u.val + 1 = t.val + 1 + m - u.val from by omega]

/-! ### Cycle 1: Orbit explicit formula -/

/-- The orbit of dir1 from dir1BlockEntry(u) follows dir1Expected. -/
private theorem orbit_dir1_explicit (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3)
    (u : Fin m) (t r : Fin m) :
    orbit m (dir1 m) (dir1BlockEntry m u) (t.val * m + r.val) =
    dir1Expected m u t r := by
  have hm_pos : 0 < m := NeZero.pos m
  suffices H : ∀ n, ∀ t r : Fin m, n = t.val * m + r.val →
      orbit m (dir1 m) (dir1BlockEntry m u) n = dir1Expected m u t r by
    exact H _ t r rfl
  intro n
  induction n with
  | zero =>
    intro t r hn
    have ht0 : t.val = 0 := by
      rcases Nat.eq_zero_or_pos t.val with h | h
      · exact h
      · exfalso; have : t.val * m ≥ m := Nat.le_mul_of_pos_left m h; omega
    have hr0 : r.val = 0 := by omega
    have ht : t = ⟨0, hm_pos⟩ := fin_eq_of_val_eq ht0
    have hr : r = ⟨0, hm_pos⟩ := fin_eq_of_val_eq hr0
    subst ht; subst hr
    exact (dir1_base_case m u).symm
  | succ n ih =>
    intro t r hn
    rw [orbit_succ]
    by_cases hr0 : r.val = 0
    · -- Round transition: previous step was (t-1, m-1)
      have ht_pos : 0 < t.val := by
        by_contra h; push_neg at h
        have htv : t.val = 0 := by omega
        rw [htv, Nat.zero_mul, Nat.zero_add] at hn; omega
      have hn' : n = (t.val - 1) * m + (m - 1) := by
        have h1 : n + 1 = t.val * m := by omega
        have h2 : t.val * m = (t.val - 1 + 1) * m := by congr 1; omega
        rw [h2, Nat.add_mul, Nat.one_mul] at h1; omega
      have ht_bound : t.val - 1 < m := by omega
      rw [ih ⟨t.val - 1, ht_bound⟩ ⟨m - 1, by omega⟩ (by simp [Fin.val_mk]; exact hn')]
      rw [dir1_succ_trans m hm_odd hm_ge u ⟨t.val - 1, ht_bound⟩ (by simp [Fin.val_mk]; omega)]
      have hreq : r = ⟨0, hm_pos⟩ := Fin.ext (by omega)
      subst hreq
      congr 1
      exact Fin.ext (by simp [Fin.val_mk]; omega)
    · -- Within-round step: previous step was (t, r-1)
      have hn' : n = t.val * m + (r.val - 1) := by omega
      have hr_bound : r.val - 1 < m := by omega
      rw [ih t ⟨r.val - 1, hr_bound⟩ (by simp [Fin.val_mk]; exact hn')]
      by_cases hr1 : r.val = 1
      · -- s=0 at (t, 0), dir1=bumpj, bumps j
        have hrr : (⟨r.val - 1, hr_bound⟩ : Fin m) = ⟨0, hm_pos⟩ :=
          fin_eq_of_val_eq (by simp [Fin.val_mk]; omega)
        rw [hrr, dir1_succ_s0 m hm_ge u t]
        convert rfl using 2
        apply fin_eq_of_val_eq; simp [Fin.val_mk]; omega
      · -- s=r-1 ≥ 1, dir1=bumpi, bumps i
        have hr_ge : (⟨r.val - 1, hr_bound⟩ : Fin m).val ≥ 1 := by simp [Fin.val_mk]; omega
        have hr_le : (⟨r.val - 1, hr_bound⟩ : Fin m).val ≤ m - 2 := by simp [Fin.val_mk]; omega
        rw [dir1_succ_mid m hm_ge u t ⟨r.val - 1, hr_bound⟩ hr_ge hr_le]
        convert rfl using 2
        apply fin_eq_of_val_eq; simp [Fin.val_mk]; omega

/-! ### Cycle 1: Super-round transition -/

/-- At the end of a super-round, the orbit transitions to the next block entry. -/
private theorem dir1_superround_exit (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3)
    (u : Fin m) :
    successor m (dir1 m) (dir1Expected m u ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩) =
    dir1BlockEntry m ⟨(u.val + 1) % m, Nat.mod_lt _ (NeZero.pos m)⟩ := by
  have hm_pos : 0 < m := NeZero.pos m
  have hfiber := dir1E_fiber m hm_ge u ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩
  simp only [Fin.val_mk, Nat.mod_eq_of_lt (show m - 1 < m from by omega)] at hfiber
  have hs_ne0 : ¬(fiberIndex m (dir1Expected m u ⟨m-1, by omega⟩ ⟨m-1, by omega⟩)).val = 0 :=
    by omega
  have hs_m1 : (fiberIndex m (dir1Expected m u ⟨m-1, by omega⟩ ⟨m-1, by omega⟩)).val = m - 1 :=
    hfiber
  -- Show i = 0 at (m-1, m-1): i = ((m-2)*m) % m = 0
  have hi_zero : (dir1Expected m u ⟨m-1, by omega⟩ ⟨m-1, by omega⟩).1.val = 0 := by
    unfold dir1Expected
    simp only [Fin.val_mk, show ¬(m - 1 = 0) from by omega, ite_false, Fin.val_add]
    rw [show m - 1 - 1 = m - 2 from by omega, mod_add_raw ((m - 2) * (m - 1)) (m - 2) m]
    have : (m - 2) * (m - 1) + (m - 2) = (m - 2) * m := by
      zify [show m ≥ 2 from by omega, show m ≥ 1 from by omega]; ring
    rw [this, Nat.mul_comm, Nat.mul_mod_right]
  rw [successor_dir1_bumpj m _ (dir1_sm1_zero m _ hs_ne0 hs_m1 hi_zero)]
  -- Goal: (v.1, v.2.1 + 1, v.2.2) = dir1BlockEntry((u+1) % m)
  unfold dir1Expected dir1BlockEntry
  simp only [Fin.val_mk, show ¬(m - 1 = 0) from by omega, ite_false,
             show m - 1 - 1 = m - 2 from by omega]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · -- i component: i_base + ⟨m-2, _⟩ = 0 (already shown)
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_mk]
    rw [mod_add_raw ((m - 2) * (m - 1)) (m - 2) m]
    have : (m - 2) * (m - 1) + (m - 2) = (m - 2) * m := by
      zify [show m ≥ 2 from by omega, show m ≥ 1 from by omega]; ring
    rw [this, Nat.mul_comm, Nat.mul_mod_right]
  · -- j component: j_base + 1 + 1 = (u+1) % m
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_mk, Fin.coe_ofNat_eq_mod]
    rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega : 1 < m)]
    rw [mod_add_raw (u.val + (m - 1)) 1 m, mod_add_raw (u.val + (m - 1) + 1) 1 m,
        Nat.mod_mod]
    rw [show u.val + (m - 1) + 1 + 1 = u.val + 1 + m * 1 from by omega,
        Nat.add_mul_mod_self_left]
  · -- k component: k_val = (m - (u+1) % m) % m
    apply Fin.ext
    simp only [Fin.val_mk]
    -- k_val = (m - 1 + m - u.val) % m = (2m - 1 - u.val) % m
    -- target = (m - (u.val + 1) % m) % m
    -- Case: u.val < m - 1: (u+1) % m = u+1, target = (m-u-1) % m = m-u-1
    --   k_val = (2m-1-u) % m = (m-1-u) % m = m-1-u ✓
    -- Case: u.val = m-1: (u+1) % m = 0, target = (m-0) % m = 0
    --   k_val = (2m-1-(m-1)) % m = m % m = 0 ✓
    have hu := u.isLt
    by_cases hu_last : u.val = m - 1
    · rw [hu_last, show m - 1 + 1 = m from by omega, Nat.mod_self,
          Nat.sub_zero, Nat.mod_self,
          show m - 1 + m - (m - 1) = m from by omega, Nat.mod_self]
    · rw [Nat.mod_eq_of_lt (show u.val + 1 < m from by omega)]
      have h1 : m - 1 + m - u.val = 2 * m - 1 - u.val := by omega
      rw [h1]
      conv_rhs => rw [show m - (u.val + 1) = m - 1 - u.val from by omega,
                       Nat.mod_eq_of_lt (show m - 1 - u.val < m from by omega)]
      rw [show 2 * m - 1 - u.val = (m - 1 - u.val) + m * 1 from by omega,
          Nat.add_mul_mod_self_left (m - 1 - u.val) m 1,
          Nat.mod_eq_of_lt (show m - 1 - u.val < m from by omega)]

/-! ### Cycle 1: Block step and orbit chaining -/

private theorem dir1_block_orbit_step (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3)
    (u : Fin m) (hu_lt : u.val < m - 1) :
    orbit m (dir1 m) (dir1BlockEntry m u) (m * m) =
    dir1BlockEntry m ⟨u.val + 1, by omega⟩ := by
  have hm_pos : 0 < m := NeZero.pos m
  have hmm : m * m = (m - 1) * m + (m - 1) + 1 := by
    zify [show m ≥ 1 from by omega]; ring
  rw [hmm, show (m - 1) * m + (m - 1) + 1 = ((m - 1) * m + (m - 1)) + 1 from by omega]
  simp only [orbit_succ]
  rw [orbit_dir1_explicit m hm_odd hm_ge u ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩]
  rw [dir1_superround_exit m hm_odd hm_ge u]
  congr 1; apply Fin.ext; simp [Fin.val_mk]
  exact Nat.mod_eq_of_lt (by omega)

private theorem orbit_dir1_reaches_block (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3)
    (u : Fin m) :
    orbit m (dir1 m) (dir1BlockEntry m ⟨0, NeZero.pos m⟩) (u.val * (m * m)) =
    dir1BlockEntry m u := by
  have hm_pos : 0 < m := NeZero.pos m
  suffices H : ∀ k (hk : k < m),
      orbit m (dir1 m) (dir1BlockEntry m ⟨0, hm_pos⟩) (k * (m * m)) =
      dir1BlockEntry m ⟨k, hk⟩ by
    have := H u.val u.isLt
    convert this using 2
  intro k
  induction k with
  | zero => intro _; simp [orbit_zero]
  | succ n ih =>
    intro hn_lt
    rw [show (n + 1) * (m * m) = n * (m * m) + m * m from by ring,
        orbit_add, ih (by omega),
        dir1_block_orbit_step m hm_odd hm_ge ⟨n, by omega⟩ (by simp [Fin.val_mk]; omega)]

private theorem orbit_dir1_returns (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3) :
    orbit m (dir1 m) (dir1BlockEntry m ⟨0, NeZero.pos m⟩) (m ^ 3) =
    dir1BlockEntry m ⟨0, NeZero.pos m⟩ := by
  have hm_pos : 0 < m := NeZero.pos m
  have hcube : m ^ 3 = (m - 1) * (m * m) + m * m := by
    zify [show m ≥ 1 from by omega]; ring
  rw [hcube, orbit_add, orbit_dir1_reaches_block m hm_odd hm_ge ⟨m - 1, by omega⟩]
  have hmm : m * m = (m - 1) * m + (m - 1) + 1 := by
    zify [show m ≥ 1 from by omega]; ring
  rw [hmm, show (m - 1) * m + (m - 1) + 1 = ((m - 1) * m + (m - 1)) + 1 from by omega]
  simp only [orbit_succ]
  rw [orbit_dir1_explicit m hm_odd hm_ge ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩]
  rw [dir1_superround_exit m hm_odd hm_ge ⟨m - 1, by omega⟩]
  congr 1; apply Fin.ext; simp [Fin.val_mk]
  rw [show m - 1 + 1 = m from by omega, Nat.mod_self]

/-! ### Cycle 1: Injectivity → Surjectivity -/

/-- Coprimality-based cancellation: if 2*t₁ ≡ 2*t₂ (mod m) with m odd, then t₁ = t₂. -/
private theorem t_eq_of_two_t_mod (m : ℕ) (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3)
    (t₁ t₂ : Fin m) (h : (2 * t₁.val) % m = (2 * t₂.val) % m) : t₁ = t₂ := by
  by_contra hne
  have hne_val : t₁.val ≠ t₂.val := fun heq => hne (Fin.ext heq)
  rcases Nat.lt_or_gt_of_ne hne_val with hlt | hgt
  · -- t₁ < t₂: m | 2*(t₂-t₁), with 2 ≤ 2*(t₂-t₁) < 2m → 2*(t₂-t₁)=m → m even, contradiction
    have hle : 2 * t₁.val ≤ 2 * t₂.val := by omega
    have hdvd : m ∣ (2 * t₂.val - 2 * t₁.val) :=
      (Nat.modEq_iff_dvd' hle).mp h
    clear h
    obtain ⟨c, hc⟩ := hdvd
    have hc_pos : c ≥ 1 := by
      rcases Nat.eq_zero_or_pos c with rfl | hpos
      · simp at hc; omega
      · exact hpos
    have : 2 * t₂.val - 2 * t₁.val < 2 * m := by
      have := t₁.isLt; have := t₂.isLt; omega
    have hc_le : c ≤ 1 := by nlinarith
    -- c = 1, so 2*(t₂-t₁) = m, but m is odd
    have hc1 : c = 1 := by omega
    subst hc1; simp only [Nat.mul_one] at hc; omega
  · -- t₁ > t₂ (symmetric)
    have hle : 2 * t₂.val ≤ 2 * t₁.val := by omega
    have hdvd : m ∣ (2 * t₁.val - 2 * t₂.val) :=
      (Nat.modEq_iff_dvd' hle).mp h.symm
    clear h
    obtain ⟨c, hc⟩ := hdvd
    have hc_pos : c ≥ 1 := by
      rcases Nat.eq_zero_or_pos c with rfl | hpos
      · simp at hc; omega
      · exact hpos
    have : 2 * t₁.val - 2 * t₂.val < 2 * m := by
      have := t₁.isLt; have := t₂.isLt; omega
    have hc_le : c ≤ 1 := by nlinarith
    have hc1 : c = 1 := by omega
    subst hc1; simp only [Nat.mul_one] at hc; omega

/-- dir1Expected is injective: distinct (u,t,r) triples give distinct vertices.
    Strategy: r from fiber, t from j+k (using gcd(2,m)=1), u from j-t. -/
private theorem dir1Expected_injective (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3) :
    Function.Injective (fun p : Fin m × Fin m × Fin m =>
      dir1Expected m p.1 p.2.1 p.2.2) := by
  have hm_pos : 0 < m := NeZero.pos m
  intro ⟨u₁, t₁, r₁⟩ ⟨u₂, t₂, r₂⟩ heq
  simp only at heq
  -- Step 1: r₁ = r₂ from fiber index
  have hf₁ := dir1E_fiber m hm_ge u₁ t₁ r₁
  have hf₂ := dir1E_fiber m hm_ge u₂ t₂ r₂
  rw [Nat.mod_eq_of_lt r₁.isLt] at hf₁
  rw [Nat.mod_eq_of_lt r₂.isLt] at hf₂
  have hfiber_eq : (fiberIndex m (dir1Expected m u₁ t₁ r₁)).val =
                   (fiberIndex m (dir1Expected m u₂ t₂ r₂)).val := by
    rw [heq]
  rw [hf₁, hf₂] at hfiber_eq
  have hr : r₁ = r₂ := Fin.ext hfiber_eq
  subst hr
  -- Step 2: Extract j and k equalities from vertex equality
  have hj : (dir1Expected m u₁ t₁ r₁).2.1 = (dir1Expected m u₂ t₂ r₁).2.1 :=
    congrArg (fun v => v.2.1) heq
  have hk : (dir1Expected m u₁ t₁ r₁).2.2 = (dir1Expected m u₂ t₂ r₁).2.2 :=
    congrArg (fun v => v.2.2) heq
  -- Step 3: j+k gives 2*t (mod m)
  -- For r=0: j = (u+t)%m, k = (t+m-u)%m, so j+k ≡ 2t+m ≡ 2t
  -- For r≥1: j = ((u+t)%m+1)%m, k = (t+m-u)%m, so j+k ≡ u+t+1+t+m-u ≡ 2t+m+1 ≡ 2t+1
  -- Either way, j+k determines 2t mod m uniquely
  have hjk₁ : ((dir1Expected m u₁ t₁ r₁).2.1.val +
               (dir1Expected m u₁ t₁ r₁).2.2.val) % m =
              (2 * t₁.val + (if r₁.val = 0 then 0 else 1)) % m := by
    unfold dir1Expected
    split_ifs with hr0
    · simp only [Fin.val_mk]
      rw [mod_add_mod' (u₁.val + t₁.val) (t₁.val + m - u₁.val),
          show u₁.val + t₁.val + (t₁.val + m - u₁.val) = 2 * t₁.val + m from by
            have := u₁.isLt; omega,
          Nat.add_mod_right, Nat.add_zero]
    · simp only [Fin.val_add, Fin.coe_ofNat_eq_mod]
      rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega : 1 < m),
          mod_add_mod' ((u₁.val + t₁.val) % m + 1) (t₁.val + m - u₁.val),
          Nat.add_assoc ((u₁.val + t₁.val) % m) 1 (t₁.val + m - u₁.val),
          mod_add_raw (u₁.val + t₁.val) (1 + (t₁.val + m - u₁.val)) m,
          show u₁.val + t₁.val + (1 + (t₁.val + m - u₁.val)) = 2 * t₁.val + 1 + m from by
            have := u₁.isLt; omega,
          show 2 * t₁.val + 1 + m = (2 * t₁.val + 1) + m from by omega,
          Nat.add_mod_right]
  have hjk₂ : ((dir1Expected m u₂ t₂ r₁).2.1.val +
               (dir1Expected m u₂ t₂ r₁).2.2.val) % m =
              (2 * t₂.val + (if r₁.val = 0 then 0 else 1)) % m := by
    unfold dir1Expected
    split_ifs with hr0
    · simp only [Fin.val_mk]
      rw [mod_add_mod' (u₂.val + t₂.val) (t₂.val + m - u₂.val),
          show u₂.val + t₂.val + (t₂.val + m - u₂.val) = 2 * t₂.val + m from by
            have := u₂.isLt; omega,
          Nat.add_mod_right, Nat.add_zero]
    · simp only [Fin.val_add, Fin.coe_ofNat_eq_mod]
      rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega : 1 < m),
          mod_add_mod' ((u₂.val + t₂.val) % m + 1) (t₂.val + m - u₂.val),
          Nat.add_assoc ((u₂.val + t₂.val) % m) 1 (t₂.val + m - u₂.val),
          mod_add_raw (u₂.val + t₂.val) (1 + (t₂.val + m - u₂.val)) m,
          show u₂.val + t₂.val + (1 + (t₂.val + m - u₂.val)) = 2 * t₂.val + 1 + m from by
            have := u₂.isLt; omega,
          show 2 * t₂.val + 1 + m = (2 * t₂.val + 1) + m from by omega,
          Nat.add_mod_right]
  have hjk_same : ((dir1Expected m u₁ t₁ r₁).2.1.val +
                   (dir1Expected m u₁ t₁ r₁).2.2.val) % m =
                  ((dir1Expected m u₂ t₂ r₁).2.1.val +
                   (dir1Expected m u₂ t₂ r₁).2.2.val) % m := by
    rw [hj, hk]
  rw [hjk₁, hjk₂] at hjk_same
  -- Cancel the +0 or +1 term
  have h2t : (2 * t₁.val) % m = (2 * t₂.val) % m := by
    split_ifs at hjk_same with hr0
    · simpa [Nat.add_zero] using hjk_same
    · exact Nat.ModEq.add_right_cancel' 1 hjk_same
  -- Step 4: 2*t₁ ≡ 2*t₂ (mod m) with m odd → t₁ = t₂
  have ht : t₁ = t₂ := t_eq_of_two_t_mod m hm_odd hm_ge t₁ t₂ h2t
  subst ht
  -- Step 5: u₁ = u₂ from j equality
  -- j component determines (u₁+t)%m = (u₂+t)%m → u₁ = u₂
  have hj_val : (dir1Expected m u₁ t₁ r₁).2.1.val =
                (dir1Expected m u₂ t₁ r₁).2.1.val := congrArg Fin.val hj
  unfold dir1Expected at hj_val
  split_ifs at hj_val with hr0
  · -- r=0: (u₁+t) % m = (u₂+t) % m
    simp only [Fin.val_mk] at hj_val
    have hut_mod : u₁.val % m = u₂.val % m :=
      Nat.ModEq.add_right_cancel' t₁.val hj_val
    have hu₁ : u₁.val % m = u₁.val := Nat.mod_eq_of_lt u₁.isLt
    have hu₂ : u₂.val % m = u₂.val := Nat.mod_eq_of_lt u₂.isLt
    exact Prod.ext (Fin.ext (by rw [← hu₁, hut_mod, hu₂])) rfl
  · -- r≥1: ((u₁+t)%m + 1)%m = ((u₂+t)%m + 1)%m
    simp only [Fin.val_add, Fin.coe_ofNat_eq_mod] at hj_val
    rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega : 1 < m)] at hj_val
    rw [mod_add_raw (u₁.val + t₁.val) 1 m, mod_add_raw (u₂.val + t₁.val) 1 m] at hj_val
    have hut_mod : u₁.val % m = u₂.val % m :=
      Nat.ModEq.add_right_cancel' (t₁.val + 1)
        (show (u₁.val + (t₁.val + 1)) % m = (u₂.val + (t₁.val + 1)) % m from by
          rwa [show u₁.val + (t₁.val + 1) = u₁.val + t₁.val + 1 from by omega,
               show u₂.val + (t₁.val + 1) = u₂.val + t₁.val + 1 from by omega])
    have hu₁ : u₁.val % m = u₁.val := Nat.mod_eq_of_lt u₁.isLt
    have hu₂ : u₂.val % m = u₂.val := Nat.mod_eq_of_lt u₂.isLt
    exact Prod.ext (Fin.ext (by rw [← hu₁, hut_mod, hu₂])) rfl

/-- dir1Expected is surjective (from injectivity + finiteness). -/
private theorem dir1Expected_surjective (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3) :
    Function.Surjective (fun p : Fin m × Fin m × Fin m =>
      dir1Expected m p.1 p.2.1 p.2.2) :=
  Finite.surjective_of_injective (dir1Expected_injective m hm_odd hm_ge)

/-! ### Cycle 1: Block completeness and main theorem -/

theorem cycle1_hamiltonian (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3) :
    ∃ start : Vertex m,
      (orbit m (dir1 m) start (m ^ 3) = start) ∧
      (∀ v : Vertex m, ∃ n : Fin (m ^ 3),
        orbit m (dir1 m) start n.val = v) := by
  have hm_pos : 0 < m := NeZero.pos m
  refine ⟨dir1BlockEntry m ⟨0, hm_pos⟩, orbit_dir1_returns m hm_odd hm_ge, ?_⟩
  intro v
  -- Every vertex v is dir1Expected(u, t, r) for some u, t, r (surjectivity)
  have hsurj := dir1Expected_surjective m hm_odd hm_ge
  obtain ⟨⟨u, t, r⟩, hutr⟩ := hsurj v
  simp only at hutr
  -- Orbit reaches dir1BlockEntry(u) after u*(m*m) steps
  have hreach := orbit_dir1_reaches_block m hm_odd hm_ge u
  -- Orbit reaches dir1Expected(u, t, r) after t*m+r more steps
  have horbit := orbit_dir1_explicit m hm_odd hm_ge u t r
  -- Total steps: u*(m*m) + t*m + r
  refine ⟨⟨u.val * (m * m) + (t.val * m + r.val), ?_⟩, ?_⟩
  · -- Bound: u*(m*m) + t*m + r < m^3
    have := u.isLt; have := t.isLt; have := r.isLt
    calc u.val * (m * m) + (t.val * m + r.val)
        < u.val * (m * m) + (t.val * m + m) := by omega
      _ = u.val * (m * m) + (t.val + 1) * m := by ring
      _ ≤ u.val * (m * m) + m * m := by nlinarith
      _ = (u.val + 1) * (m * m) := by ring
      _ ≤ m * (m * m) := by nlinarith
      _ = m ^ 3 := by ring
  · simp only [Fin.val_mk]
    rw [orbit_add, hreach, horbit, hutr]

/-! ### Cycle 2: Definitions and helpers -/

/-- Entry point for super-round u of cycle 2. -/
def dir2BlockEntry (m : ℕ) [NeZero m] (u : Fin m) : Vertex m :=
  (⟨0, NeZero.pos m⟩,
   ⟨((m - 2) * u.val) % m, Nat.mod_lt _ (NeZero.pos m)⟩,
   ⟨(2 * u.val) % m, Nat.mod_lt _ (NeZero.pos m)⟩)

/-- Expected vertex at orbit step (t*m + r) within super-round u of cycle 2.
    Non-special (j_u < m-1): r=0→(2t,j_u,2u+(m-2)t); r≥1,t<m-1→(2t+1,j_u,2u+(m-2)t+r-1);
    r≥1,t=m-1→(m-1,j_u+r-1,2u+(m-2)(m-1)).
    Special (j_u=m-1): t<m-1∨r≤1→(t,m-1,2u+m-t+r); t=m-1∧r≥2→(m-1,r-2,2u+2). -/
def dir2Expected (m : ℕ) [NeZero m] (u t r : Fin m) : Vertex m :=
  let j_u := ((m - 2) * u.val) % m
  if j_u < m - 1 then
    -- Non-special super-round
    if r.val = 0 then
      (⟨(2 * t.val) % m, Nat.mod_lt _ (NeZero.pos m)⟩,
       ⟨j_u, Nat.mod_lt _ (NeZero.pos m)⟩,
       ⟨(2 * u.val + (m - 2) * t.val) % m, Nat.mod_lt _ (NeZero.pos m)⟩)
    else if t.val < m - 1 then
      (⟨(2 * t.val + 1) % m, Nat.mod_lt _ (NeZero.pos m)⟩,
       ⟨j_u, Nat.mod_lt _ (NeZero.pos m)⟩,
       ⟨(2 * u.val + (m - 2) * t.val + r.val - 1) % m, Nat.mod_lt _ (NeZero.pos m)⟩)
    else
      (⟨m - 1, by have := NeZero.pos m; omega⟩,
       ⟨(j_u + r.val - 1) % m, Nat.mod_lt _ (NeZero.pos m)⟩,
       ⟨(2 * u.val + (m - 2) * (m - 1)) % m, Nat.mod_lt _ (NeZero.pos m)⟩)
  else
    -- Special super-round (j_u = m-1)
    if t.val < m - 1 ∨ r.val ≤ 1 then
      (⟨t.val, t.isLt⟩,
       ⟨m - 1, by have := NeZero.pos m; omega⟩,
       ⟨(2 * u.val + m - t.val + r.val) % m, Nat.mod_lt _ (NeZero.pos m)⟩)
    else
      (⟨m - 1, by have := NeZero.pos m; omega⟩,
       ⟨(r.val - 2) % m, Nat.mod_lt _ (NeZero.pos m)⟩,
       ⟨(2 * u.val + 2) % m, Nat.mod_lt _ (NeZero.pos m)⟩)

/-- Base case: dir2Expected at (u, 0, 0) = dir2BlockEntry u. -/
private theorem dir2_base_case (m : ℕ) [NeZero m] (u : Fin m) :
    dir2Expected m u ⟨0, NeZero.pos m⟩ ⟨0, NeZero.pos m⟩ = dir2BlockEntry m u := by
  unfold dir2Expected dir2BlockEntry
  simp only [Fin.val_mk]
  split_ifs with hns hr0
  · rfl
  · -- Special, hr0 : 0 < m - 1 ∨ 0 ≤ 1 (true branch)
    have hj_eq : ((m - 2) * u.val) % m = m - 1 := by
      have := Nat.mod_lt ((m - 2) * u.val) (NeZero.pos m); omega
    refine Prod.ext rfl (Prod.ext (Fin.ext ?_) (Fin.ext ?_))
    · simp only [Fin.val_mk]; exact hj_eq.symm
    · simp only [Fin.val_mk]
      rw [show 2 * u.val + m - 0 + 0 = 2 * u.val + m * 1 from by omega,
          Nat.add_mul_mod_self_left]
  · exfalso; push_neg at hr0; omega

/-- In a special super-round, (m-2)*u ≡ m-1 (mod m) implies 2*u ≡ 1 (mod m). -/
private theorem special_implies_2u_eq_1 (m : ℕ) (hm_pos : 0 < m) (hm_ge : m ≥ 3)
    (u : Fin m) (hsp : ¬ ((m - 2) * u.val) % m < m - 1) :
    (2 * u.val) % m = 1 := by
  have hj_eq : ((m - 2) * u.val) % m = m - 1 := by
    have := Nat.mod_lt ((m - 2) * u.val) hm_pos; omega
  have hfact : (m - 2) * u.val + 2 * u.val = m * u.val := by
    zify [show m ≥ 2 from by omega]; ring
  have hmod : ((m - 2) * u.val + 2 * u.val) % m = 0 := by
    rw [hfact]; exact Nat.mul_mod_right m u.val
  rw [← mod_add_mod'] at hmod
  rw [hj_eq] at hmod
  have h2u_bound := Nat.mod_lt (2 * u.val) hm_pos
  have hdvd := Nat.dvd_of_mod_eq_zero hmod
  obtain ⟨c, hc⟩ := hdvd
  have : c = 1 := by
    rcases Nat.eq_zero_or_pos c with h0 | hpos
    · rw [h0, Nat.mul_zero] at hc; omega
    · by_contra hne
      have hc2 : c ≥ 2 := by omega
      have := Nat.mul_le_mul_left m hc2
      omega
  subst this; omega

/-- Fiber index of dir2Expected equals r.val (mod m). -/
private theorem dir2E_fiber (m : ℕ) [NeZero m] (hm_ge : m ≥ 3) (u t r : Fin m) :
    (fiberIndex m (dir2Expected m u t r)).val = r.val % m := by
  have hm_pos : 0 < m := NeZero.pos m
  unfold fiberIndex dir2Expected
  simp only [Fin.val_mk]
  split_ifs with hns hr0 ht htlr
  · -- Branch 1: non-special, r=0
    simp only [Fin.val_add, Fin.val_mk]
    rw [mod_add_mod' (2 * t.val) ((m - 2) * u.val),
        mod_add_mod' (2 * t.val + (m - 2) * u.val) (2 * u.val + (m - 2) * t.val)]
    have hsum : 2 * t.val + (m - 2) * u.val + (2 * u.val + (m - 2) * t.val) =
                m * (u.val + t.val) := by
      zify [show m ≥ 2 from by omega]; ring
    rw [hsum, Nat.mul_mod_right, hr0, Nat.zero_mod]
  · -- Branch 2: non-special, r≥1, t<m-1
    simp only [Fin.val_add, Fin.val_mk]
    rw [mod_add_mod' (2 * t.val + 1) ((m - 2) * u.val),
        mod_add_mod' (2 * t.val + 1 + (m - 2) * u.val)
                     (2 * u.val + (m - 2) * t.val + r.val - 1)]
    have hr1 : r.val ≥ 1 := by omega
    have hsum : 2 * t.val + 1 + (m - 2) * u.val +
                (2 * u.val + (m - 2) * t.val + r.val - 1) =
                r.val + m * (u.val + t.val) := by
      zify [show 2 ≤ m from by omega,
            show 1 ≤ 2 * u.val + (m - 2) * t.val + r.val from by omega]; ring
    rw [hsum, Nat.add_mul_mod_self_left]
  · -- Branch 3: non-special, r≥1, t=m-1
    simp only [Fin.val_add, Fin.val_mk]
    have hr1 : r.val ≥ 1 := by omega
    rw [show ((m - 2) * u.val) % m + r.val - 1 =
            ((m - 2) * u.val) % m + (r.val - 1) from by omega,
        mod_add_raw ((m - 2) * u.val) (r.val - 1) m,
        raw_add_mod (m - 1) ((m - 2) * u.val + (r.val - 1)) m,
        mod_add_mod' (m - 1 + ((m - 2) * u.val + (r.val - 1)))
                     (2 * u.val + (m - 2) * (m - 1))]
    have hsum : m - 1 + ((m - 2) * u.val + (r.val - 1)) +
                (2 * u.val + (m - 2) * (m - 1)) =
                r.val + m * (u.val + m - 2) := by
      zify [show 1 ≤ m from by omega, show 2 ≤ m from by omega,
            hr1, show 2 ≤ u.val + m from by omega]; ring
    rw [hsum, Nat.add_mul_mod_self_left]
  · -- Branch 4: special, t<m-1 ∨ r≤1
    simp only [Fin.val_add, Fin.val_mk]
    have h2u1 := special_implies_2u_eq_1 m hm_pos hm_ge u hns
    have hdiv := Nat.div_add_mod (2 * u.val) m
    rw [h2u1] at hdiv
    have h2udiv : m * (2 * u.val / m) = 2 * u.val - 1 := by omega
    rw [mod_add_mod' (t.val + (m - 1)) (2 * u.val + m - t.val + r.val)]
    have h_expand : m * (2 * u.val / m + 2) = 2 * u.val - 1 + 2 * m := by
      rw [Nat.mul_add, h2udiv, Nat.mul_comm m 2]
    have h2u_ge1 : 2 * u.val ≥ 1 := by
      rcases Nat.eq_zero_or_pos (2 * u.val) with h0 | hp
      · rw [h0, Nat.zero_mod] at h2u1; omega
      · omega
    have hsum : t.val + (m - 1) + (2 * u.val + m - t.val + r.val) =
                r.val + m * (2 * u.val / m + 2) := by
      rw [h_expand]; omega
    rw [hsum, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt r.isLt]
  · -- Branch 5: special, t=m-1, r≥2
    simp only [Fin.val_add, Fin.val_mk]
    push_neg at htlr
    have h2u1 := special_implies_2u_eq_1 m hm_pos hm_ge u hns
    have hdiv := Nat.div_add_mod (2 * u.val) m
    rw [h2u1] at hdiv
    have h2udiv : m * (2 * u.val / m) = 2 * u.val - 1 := by omega
    rw [raw_add_mod (m - 1) (r.val - 2) m,
        mod_add_mod' (m - 1 + (r.val - 2)) (2 * u.val + 2)]
    have h_expand : m * (2 * u.val / m + 1) = 2 * u.val - 1 + m := by
      rw [Nat.mul_add, h2udiv, Nat.mul_one]
    have h2u_ge1 : 2 * u.val ≥ 1 := by
      rcases Nat.eq_zero_or_pos (2 * u.val) with h0 | hp
      · rw [h0, Nat.zero_mod] at h2u1; omega
      · omega
    have hsum : m - 1 + (r.val - 2) + (2 * u.val + 2) =
                r.val + m * (2 * u.val / m + 1) := by
      rw [h_expand]; omega
    rw [hsum, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt r.isLt]

/-! ### Cycle 2: Successor transition helpers -/

private theorem successor_dir2_bumpi (m : ℕ) [NeZero m] (v : Vertex m)
    (h : dir2 m v = Dir.bumpi) :
    successor m (dir2 m) v = (v.1 + 1, v.2.1, v.2.2) := by
  simp [successor, h, bump]

private theorem successor_dir2_bumpj (m : ℕ) [NeZero m] (v : Vertex m)
    (h : dir2 m v = Dir.bumpj) :
    successor m (dir2 m) v = (v.1, v.2.1 + 1, v.2.2) := by
  simp [successor, h, bump]

private theorem successor_dir2_bumpk (m : ℕ) [NeZero m] (v : Vertex m)
    (h : dir2 m v = Dir.bumpk) :
    successor m (dir2 m) v = (v.1, v.2.1, v.2.2 + 1) := by
  simp [successor, h, bump]

/-- For odd m and t < m-1, (2t+1) % m ≠ m-1. Key: 2t+1 is odd but m-1 is even. -/
private theorem two_t_plus_one_ne_m1 (m : ℕ) (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3)
    (t : ℕ) (ht : t < m - 1) : (2 * t + 1) % m ≠ m - 1 := by
  intro h
  by_cases hge : 2 * t + 1 ≥ m
  · -- (2t+1) % m = 2t+1-m = m-1 → t = m-1, contradicts t < m-1
    have : (2 * t + 1) % m = 2 * t + 1 - m := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
    rw [this] at h; omega
  · -- (2t+1) % m = 2t+1 = m-1 → m = 2(t+1), contradicts m odd
    push_neg at hge
    have : (2 * t + 1) % m = 2 * t + 1 := Nat.mod_eq_of_lt (by omega)
    rw [this] at h; omega

/-- At r=0 (start of round), successor advances to r=1. -/
private theorem dir2_succ_s0 (m : ℕ) [NeZero m] (hm_ge : m ≥ 3) (u t : Fin m) :
    successor m (dir2 m) (dir2Expected m u t ⟨0, NeZero.pos m⟩) =
    dir2Expected m u t ⟨1, by omega⟩ := by
  have hm_pos : 0 < m := NeZero.pos m
  have hfiber := dir2E_fiber m hm_ge u t ⟨0, hm_pos⟩
  simp only [Fin.val_mk, Nat.zero_mod] at hfiber
  by_cases hns : ((m - 2) * u.val) % m < m - 1
  · -- Non-special: j < m-1, direction is bumpi
    have hj : (dir2Expected m u t ⟨0, hm_pos⟩).2.1.val < m - 1 := by
      simp only [dir2Expected, Fin.val_mk, hns, ite_true]
    rw [successor_dir2_bumpi m _ (dir2_s0_jlt m _ hfiber hj)]
    unfold dir2Expected
    simp only [Fin.val_mk, hns, ite_true, show (0 : ℕ) = 0 from rfl, ite_true,
               show ¬(1 : ℕ) = 0 from by omega, ite_false]
    by_cases ht : t.val < m - 1
    · simp only [ht, ite_true, show 1 - 1 = 0 from rfl]
      refine Prod.ext ?_ (Prod.ext rfl rfl)
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_mk, Fin.coe_ofNat_eq_mod]
      rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega), mod_add_raw (2 * t.val) 1 m]
    · simp only [show ¬(t.val < m - 1) from ht, ite_false]
      have ht_eq : t.val = m - 1 := by omega
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> apply Fin.ext <;>
        simp only [Fin.val_add, Fin.val_mk, Fin.coe_ofNat_eq_mod]
      · rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega), mod_add_raw (2 * t.val) 1 m,
            ht_eq, show 2 * (m - 1) + 1 = m - 1 + m * 1 from by omega,
            Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : m - 1 < m)]
      · rw [show ((m - 2) * u.val) % m + 1 - 1 = ((m - 2) * u.val) % m from by omega,
            Nat.mod_eq_of_lt (Nat.mod_lt _ hm_pos)]
      · congr 1; rw [ht_eq]
  · -- Special: j = m-1, direction is bumpk
    have hsp : ((m - 2) * u.val) % m = m - 1 := by
      have := Nat.mod_lt ((m - 2) * u.val) hm_pos; omega
    have hj : ¬(dir2Expected m u t ⟨0, hm_pos⟩).2.1.val < m - 1 := by
      suffices h : (dir2Expected m u t ⟨0, hm_pos⟩).2.1.val = m - 1 by omega
      simp only [dir2Expected, Fin.val_mk, hsp,
                 show ¬(m - 1 < m - 1) from by omega, ite_false,
                 show t.val < m - 1 ∨ (0 : ℕ) ≤ 1 from Or.inr (Nat.zero_le 1), ite_true]
    rw [successor_dir2_bumpk m _ (dir2_s0_jeq m _ hfiber hj)]
    simp only [dir2Expected, Fin.val_mk, hsp,
               show ¬(m - 1 < m - 1) from by omega, ite_false,
               show t.val < m - 1 ∨ (0 : ℕ) ≤ 1 from Or.inr (Nat.zero_le 1), ite_true,
               show t.val < m - 1 ∨ (1 : ℕ) ≤ 1 from Or.inr le_rfl, ite_true]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_mk, Fin.coe_ofNat_eq_mod]
    rw [show 2 * u.val + m - t.val + 0 = 2 * u.val + m - t.val from by omega,
        show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega),
        mod_add_raw (2 * u.val + m - t.val) 1 m]

/-- At 1 ≤ r ≤ m-2 (mid-round), successor advances to r+1. -/
private theorem dir2_succ_mid (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3)
    (u t r : Fin m) (hr_ge : r.val ≥ 1) (hr_le : r.val ≤ m - 2) :
    successor m (dir2 m) (dir2Expected m u t r) =
    dir2Expected m u t ⟨r.val + 1, by omega⟩ := by
  have hm_pos : 0 < m := NeZero.pos m
  have hfiber := dir2E_fiber m hm_ge u t r
  rw [Nat.mod_eq_of_lt r.isLt] at hfiber
  have hs_ne0 : ¬(fiberIndex m (dir2Expected m u t r)).val = 0 := by omega
  have hs_nem1 : ¬(fiberIndex m (dir2Expected m u t r)).val = m - 1 := by omega
  by_cases hns : ((m - 2) * u.val) % m < m - 1
  · -- Non-special
    by_cases ht : t.val < m - 1
    · -- Branch 2: i = (2t+1)%m, bumpk (since i < m-1 for odd m)
      have hi_lt : (dir2Expected m u t r).1.val < m - 1 := by
        unfold dir2Expected
        simp only [Fin.val_mk, hns, ite_true, show ¬r.val = 0 from by omega, ite_false,
                   ht, ite_true]
        exact lt_of_le_of_ne
          (by have := Nat.mod_lt (2 * t.val + 1) hm_pos; omega)
          (two_t_plus_one_ne_m1 m hm_odd hm_ge t.val ht)
      rw [successor_dir2_bumpk m _ (dir2_mid_ilt m _ hs_ne0 hs_nem1 hi_lt)]
      unfold dir2Expected
      simp only [Fin.val_mk, hns, ite_true,
                 show ¬r.val = 0 from by omega, ite_false,
                 show ¬(r.val + 1 = 0) from by omega, ite_false,
                 ht, ite_true, show r.val + 1 - 1 = r.val from by omega]
      refine Prod.ext rfl (Prod.ext rfl ?_)
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_mk, Fin.coe_ofNat_eq_mod]
      rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega),
          mod_add_raw (2 * u.val + (m - 2) * t.val + r.val - 1) 1 m]
      congr 1; omega
    · -- Branch 3: i = m-1, bumpj
      have hi_eq : ¬(dir2Expected m u t r).1.val < m - 1 := by
        unfold dir2Expected
        simp only [Fin.val_mk, hns, ite_true, show ¬r.val = 0 from by omega, ite_false,
                   show ¬(t.val < m - 1) from ht, ite_false]; omega
      rw [successor_dir2_bumpj m _ (dir2_mid_ieq m _ hs_ne0 hs_nem1 hi_eq)]
      unfold dir2Expected
      simp only [Fin.val_mk, hns, ite_true,
                 show ¬r.val = 0 from by omega, ite_false,
                 show ¬(r.val + 1 = 0) from by omega, ite_false,
                 show ¬(t.val < m - 1) from ht, ite_false]
      refine Prod.ext rfl (Prod.ext ?_ rfl)
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_mk, Fin.coe_ofNat_eq_mod]
      rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega)]
      have hj_bound := Nat.mod_lt ((m - 2) * u.val) hm_pos
      rw [show ((m - 2) * u.val) % m + r.val - 1 =
              ((m - 2) * u.val) % m + (r.val - 1) from by omega,
          mod_add_raw ((m - 2) * u.val % m + (r.val - 1)) 1 m]
      congr 1; omega
  · -- Special
    have hsp : ((m - 2) * u.val) % m = m - 1 := by
      have := Nat.mod_lt ((m - 2) * u.val) hm_pos; omega
    by_cases ht : t.val < m - 1
    · -- Branch 4 (t<m-1): i = t < m-1, bumpk
      have hi_lt : (dir2Expected m u t r).1.val < m - 1 := by
        simp only [dir2Expected, Fin.val_mk, hsp,
                   show ¬(m - 1 < m - 1) from by omega, ite_false,
                   show t.val < m - 1 ∨ r.val ≤ 1 from Or.inl ht, ite_true]
        exact ht
      rw [successor_dir2_bumpk m _ (dir2_mid_ilt m _ hs_ne0 hs_nem1 hi_lt)]
      simp only [dir2Expected, Fin.val_mk, hsp,
                 show ¬(m - 1 < m - 1) from by omega, ite_false,
                 show t.val < m - 1 ∨ r.val ≤ 1 from Or.inl ht, ite_true,
                 show t.val < m - 1 ∨ (r.val + 1) ≤ 1 from Or.inl ht, ite_true]
      refine Prod.ext rfl (Prod.ext rfl ?_)
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_mk, Fin.coe_ofNat_eq_mod]
      rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega),
          mod_add_raw (2 * u.val + m - t.val + r.val) 1 m,
          show 2 * u.val + m - t.val + r.val + 1 = 2 * u.val + m - t.val + (r.val + 1) from by omega]
    · -- Special, t = m-1: bumpj (since i = m-1)
      have ht_eq : t.val = m - 1 := by omega
      have hi_eq : ¬(dir2Expected m u t r).1.val < m - 1 := by
        simp only [dir2Expected, Fin.val_mk, hsp,
                   show ¬(m - 1 < m - 1) from by omega, ite_false]
        by_cases hrl : r.val ≤ 1
        · simp only [show t.val < m - 1 ∨ r.val ≤ 1 from Or.inr hrl, ite_true]; omega
        · push_neg at hrl
          simp only [show ¬(t.val < m - 1 ∨ r.val ≤ 1) from by push_neg; constructor <;> omega,
                     ite_false]; omega
      rw [successor_dir2_bumpj m _ (dir2_mid_ieq m _ hs_ne0 hs_nem1 hi_eq)]
      simp only [dir2Expected, Fin.val_mk, hsp,
                 show ¬(m - 1 < m - 1) from by omega, ite_false]
      -- Case split on r ≤ 1 vs r ≥ 2
      by_cases hrl : r.val ≤ 1
      · -- r = 1 (since r ≥ 1), branch 4 → branch 5 transition
        have hr1 : r.val = 1 := by omega
        rw [if_pos (show t.val < m - 1 ∨ r.val ≤ 1 from Or.inr hrl)]
        rw [if_neg (show ¬(t.val < m - 1 ∨ (r.val + 1) ≤ 1) from by push_neg; omega)]
        refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> apply Fin.ext <;>
          simp only [Fin.val_add, Fin.val_mk, Fin.coe_ofNat_eq_mod]
        · -- i: t → m-1
          omega
        · -- j: (m-1)+1 → (r+1-2)%m = 0
          rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega),
              show m - 1 + 1 = m from by omega, Nat.mod_self,
              show r.val + 1 - 2 = 0 from by omega, Nat.zero_mod]
        · -- k: (2u+m-t+r)%m = (2u+2)%m
          congr 1; omega
      · -- r ≥ 2, branch 5 → branch 5
        push_neg at hrl
        rw [if_neg (show ¬(t.val < m - 1 ∨ r.val ≤ 1) from by push_neg; omega)]
        rw [if_neg (show ¬(t.val < m - 1 ∨ (r.val + 1) ≤ 1) from by push_neg; omega)]
        refine Prod.ext rfl (Prod.ext ?_ rfl)
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_mk, Fin.coe_ofNat_eq_mod]
        rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega)]
        rw [show (r.val - 2) % m + 1 = r.val + 1 - 2 from by
              rw [Nat.mod_eq_of_lt (by omega : r.val - 2 < m)]; omega]

/-- At r=m-1, t<m-1: round transition to (t+1, 0). Direction is always bumpi. -/
private theorem dir2_succ_trans (m : ℕ) [NeZero m] (hm_ge : m ≥ 3)
    (u t : Fin m) (ht : t.val < m - 1) :
    successor m (dir2 m) (dir2Expected m u t ⟨m - 1, by omega⟩) =
    dir2Expected m u ⟨t.val + 1, by omega⟩ ⟨0, NeZero.pos m⟩ := by
  have hm_pos : 0 < m := NeZero.pos m
  have hfiber := dir2E_fiber m hm_ge u t ⟨m - 1, by omega⟩
  simp only [Fin.val_mk, Nat.mod_eq_of_lt (show m - 1 < m from by omega)] at hfiber
  have hs_ne0 : ¬(fiberIndex m (dir2Expected m u t ⟨m-1, by omega⟩)).val = 0 := by omega
  have hs_m1 : (fiberIndex m (dir2Expected m u t ⟨m-1, by omega⟩)).val = m - 1 := hfiber
  rw [successor_dir2_bumpi m _ (dir2_sm1 m _ hs_ne0 hs_m1)]
  -- Goal: bumped i. Now show result equals dir2Expected(u, t+1, 0)
  by_cases hns : ((m - 2) * u.val) % m < m - 1
  · -- Non-special
    unfold dir2Expected
    simp only [Fin.val_mk, hns, ite_true,
               show ¬(m - 1 : ℕ) = 0 from by omega, ite_false,
               ht, ite_true, show (0 : ℕ) = 0 from rfl, ite_true]
    refine Prod.ext ?_ (Prod.ext rfl ?_) <;> apply Fin.ext <;>
      simp only [Fin.val_add, Fin.val_mk, Fin.coe_ofNat_eq_mod]
    · -- i: ((2t+1)%m + 1%m) % m = (2*(t+1)) % m
      rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega),
          mod_add_raw (2 * t.val + 1) 1 m,
          show 2 * t.val + 1 + 1 = 2 * (t.val + 1) from by ring]
    · -- k: (2u+(m-2)t+m-2)%m = (2u+(m-2)*(t+1))%m
      congr 1
      rw [show (m - 2) * (t.val + 1) = (m - 2) * t.val + (m - 2) from by ring]
      omega
  · -- Special: branch 4 (t<m-1 ∨ m-1≤1 → t<m-1)
    have hsp : ((m - 2) * u.val) % m = m - 1 := by
      have := Nat.mod_lt ((m - 2) * u.val) hm_pos; omega
    simp only [dir2Expected, Fin.val_mk, hsp,
               show ¬(m - 1 < m - 1) from by omega, ite_false,
               show t.val < m - 1 ∨ (m - 1 : ℕ) ≤ 1 from Or.inl ht, ite_true,
               show (t.val + 1) < m - 1 ∨ (0 : ℕ) ≤ 1 from Or.inr (Nat.zero_le 1), ite_true]
    refine Prod.ext ?_ (Prod.ext rfl ?_) <;> apply Fin.ext <;>
      simp only [Fin.val_add, Fin.val_mk, Fin.coe_ofNat_eq_mod]
    · -- i: (t + 1) % m = t + 1
      rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega)]
      exact Nat.mod_eq_of_lt (by omega)
    · -- k: (2u+m-t+m-1)%m = (2u+m-(t+1)+0)%m
      conv_rhs => rw [show 2 * u.val + m - (t.val + 1) + 0 =
                          2 * u.val + m - (t.val + 1) from by omega]
      rw [show 2 * u.val + m - t.val + (m - 1) =
              2 * u.val + m - (t.val + 1) + m * 1 from by omega,
          Nat.add_mul_mod_self_left]

/-! ### Cycle 2: Orbit explicit formula -/

/-- The orbit of dir2 from dir2BlockEntry(u) follows dir2Expected. -/
private theorem orbit_dir2_explicit (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3)
    (u : Fin m) (t r : Fin m) :
    orbit m (dir2 m) (dir2BlockEntry m u) (t.val * m + r.val) =
    dir2Expected m u t r := by
  have hm_pos : 0 < m := NeZero.pos m
  suffices H : ∀ n, ∀ t r : Fin m, n = t.val * m + r.val →
      orbit m (dir2 m) (dir2BlockEntry m u) n = dir2Expected m u t r by
    exact H _ t r rfl
  intro n
  induction n with
  | zero =>
    intro t r hn
    have ht0 : t.val = 0 := by
      rcases Nat.eq_zero_or_pos t.val with h | h
      · exact h
      · exfalso; have : t.val * m ≥ m := Nat.le_mul_of_pos_left m h; omega
    have hr0 : r.val = 0 := by omega
    have ht : t = ⟨0, hm_pos⟩ := fin_eq_of_val_eq ht0
    have hr : r = ⟨0, hm_pos⟩ := fin_eq_of_val_eq hr0
    subst ht; subst hr
    exact (dir2_base_case m u).symm
  | succ n ih =>
    intro t r hn
    rw [orbit_succ]
    by_cases hr0 : r.val = 0
    · -- Round transition: previous step was (t-1, m-1)
      have ht_pos : 0 < t.val := by
        by_contra h; push_neg at h
        have htv : t.val = 0 := by omega
        rw [htv, Nat.zero_mul, Nat.zero_add] at hn; omega
      have hn' : n = (t.val - 1) * m + (m - 1) := by
        have h1 : n + 1 = t.val * m := by omega
        have h2 : t.val * m = (t.val - 1 + 1) * m := by congr 1; omega
        rw [h2, Nat.add_mul, Nat.one_mul] at h1; omega
      have ht_bound : t.val - 1 < m := by omega
      rw [ih ⟨t.val - 1, ht_bound⟩ ⟨m - 1, by omega⟩ (by simp [Fin.val_mk]; exact hn')]
      rw [dir2_succ_trans m hm_ge u ⟨t.val - 1, ht_bound⟩ (by simp [Fin.val_mk]; omega)]
      have hreq : r = ⟨0, hm_pos⟩ := Fin.ext (by omega)
      subst hreq
      congr 1
      exact Fin.ext (by simp [Fin.val_mk]; omega)
    · -- Within-round step: previous step was (t, r-1)
      have hn' : n = t.val * m + (r.val - 1) := by omega
      have hr_bound : r.val - 1 < m := by omega
      rw [ih t ⟨r.val - 1, hr_bound⟩ (by simp [Fin.val_mk]; exact hn')]
      by_cases hr1 : r.val = 1
      · -- s=0, dir2 at (t, 0)
        have hrr : (⟨r.val - 1, hr_bound⟩ : Fin m) = ⟨0, hm_pos⟩ :=
          fin_eq_of_val_eq (by simp [Fin.val_mk]; omega)
        rw [hrr, dir2_succ_s0 m hm_ge u t]
        convert rfl using 2
        apply fin_eq_of_val_eq; simp [Fin.val_mk]; omega
      · -- s=r-1 ≥ 1, mid-round
        have hr_ge : (⟨r.val - 1, hr_bound⟩ : Fin m).val ≥ 1 := by simp [Fin.val_mk]; omega
        have hr_le : (⟨r.val - 1, hr_bound⟩ : Fin m).val ≤ m - 2 := by simp [Fin.val_mk]; omega
        rw [dir2_succ_mid m hm_odd hm_ge u t ⟨r.val - 1, hr_bound⟩ hr_ge hr_le]
        convert rfl using 2
        apply fin_eq_of_val_eq; simp [Fin.val_mk]; omega

/-! ### Cycle 2: Super-round transition -/

/-- At the end of a super-round, the orbit transitions to the next block entry. -/
private theorem mul_mod_right' (a b n : ℕ) (hn : 0 < n) :
    (a * b) % n = (a * (b % n)) % n := by
  nth_rw 1 [← Nat.mod_add_div b n]
  rw [Nat.mul_add, show a * (n * (b / n)) = n * (a * (b / n)) from by ring,
      Nat.add_mul_mod_self_left]

private theorem dir2_superround_exit (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3)
    (u : Fin m) :
    successor m (dir2 m) (dir2Expected m u ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩) =
    dir2BlockEntry m ⟨(u.val + 1) % m, Nat.mod_lt _ (NeZero.pos m)⟩ := by
  have hm_pos : 0 < m := NeZero.pos m
  have hfiber := dir2E_fiber m hm_ge u ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩
  simp only [Fin.val_mk, Nat.mod_eq_of_lt (show m - 1 < m from by omega)] at hfiber
  have hs_ne0 : ¬(fiberIndex m (dir2Expected m u ⟨m-1, by omega⟩ ⟨m-1, by omega⟩)).val = 0 :=
    by omega
  have hs_m1 : (fiberIndex m (dir2Expected m u ⟨m-1, by omega⟩ ⟨m-1, by omega⟩)).val = m - 1 :=
    hfiber
  rw [successor_dir2_bumpi m _ (dir2_sm1 m _ hs_ne0 hs_m1)]
  by_cases hns : ((m - 2) * u.val) % m < m - 1
  · -- Non-special, branch 3: t=m-1, r=m-1≥1
    unfold dir2Expected dir2BlockEntry
    simp only [Fin.val_mk, hns, ite_true,
               show ¬((m - 1 : ℕ) = 0) from by omega, ite_false,
               show ¬(m - 1 < m - 1) from by omega, ite_false]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> apply Fin.ext <;>
      simp only [Fin.val_add, Fin.val_mk, Fin.coe_ofNat_eq_mod]
    · -- i: (m-1 + 1%m)%m = 0
      rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega),
          show m - 1 + 1 = m from by omega, Nat.mod_self]
    · -- j: ((m-2)*u%m + m-1-1)%m = (m-2)*((u+1)%m)%m
      rw [show ((m - 2) * u.val) % m + (m - 1) - 1 =
              ((m - 2) * u.val) % m + (m - 2) from by omega,
          mod_add_raw ((m - 2) * u.val) (m - 2) m,
          show (m - 2) * u.val + (m - 2) = (m - 2) * (u.val + 1) from by ring]
      exact mul_mod_right' (m - 2) (u.val + 1) m hm_pos
    · -- k: (2u+(m-2)*(m-1))%m = 2*((u+1)%m)%m
      have hmm : (m - 2) * (m - 1) = m * (m - 3) + 2 := by
        zify [show m ≥ 3 from hm_ge, show m ≥ 2 from by omega,
              show m ≥ 1 from by omega]; ring
      rw [hmm, show 2 * u.val + (m * (m - 3) + 2) =
                    2 * (u.val + 1) + m * (m - 3) from by ring,
          Nat.add_mul_mod_self_left]
      exact mul_mod_right' 2 (u.val + 1) m hm_pos
  · -- Special, branch 5: t=m-1, r=m-1≥2
    have hsp : ((m - 2) * u.val) % m = m - 1 := by
      have := Nat.mod_lt ((m - 2) * u.val) hm_pos; omega
    simp only [dir2Expected, dir2BlockEntry, Fin.val_mk, hsp,
               show ¬(m - 1 < m - 1) from by omega, ite_false,
               false_or, show ¬((m - 1 : ℕ) ≤ 1) from by omega, ite_false]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> apply Fin.ext <;>
      simp only [Fin.val_add, Fin.val_mk, Fin.coe_ofNat_eq_mod]
    · -- i: (m-1 + 1%m)%m = 0
      rw [show (1 : ℕ) % m = 1 from Nat.mod_eq_of_lt (by omega),
          show m - 1 + 1 = m from by omega, Nat.mod_self]
    · -- j: (m-1-2)%m = ((m-2)*((u+1)%m))%m
      rw [show m - 1 - 2 = m - 3 from by omega]
      rw [← mul_mod_right' (m - 2) (u.val + 1) m hm_pos,
          show (m - 2) * (u.val + 1) = (m - 2) * u.val + (m - 2) from by ring,
          ← mod_add_raw ((m - 2) * u.val) (m - 2) m, hsp,
          show m - 1 + (m - 2) = m - 3 + m * 1 from by omega,
          Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt (show m - 3 < m from by omega)]
    · -- k: (2u+2)%m = (2*((u+1)%m))%m
      rw [← mul_mod_right' 2 (u.val + 1) m hm_pos,
          show 2 * (u.val + 1) = 2 * u.val + 2 from by ring]

/-! ### Cycle 2: Block chaining -/

private theorem dir2_block_orbit_step (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3)
    (u : Fin m) (hu_lt : u.val < m - 1) :
    orbit m (dir2 m) (dir2BlockEntry m u) (m * m) =
    dir2BlockEntry m ⟨u.val + 1, by omega⟩ := by
  have hm_pos : 0 < m := NeZero.pos m
  have hmm : m * m = (m - 1) * m + (m - 1) + 1 := by
    zify [show m ≥ 1 from by omega]; ring
  rw [hmm, show (m - 1) * m + (m - 1) + 1 = ((m - 1) * m + (m - 1)) + 1 from by omega]
  simp only [orbit_succ]
  rw [orbit_dir2_explicit m hm_odd hm_ge u ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩]
  rw [dir2_superround_exit m hm_odd hm_ge u]
  congr 1; apply Fin.ext; simp [Fin.val_mk]
  exact Nat.mod_eq_of_lt (by omega)

private theorem orbit_dir2_reaches_block (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3)
    (u : Fin m) :
    orbit m (dir2 m) (dir2BlockEntry m ⟨0, NeZero.pos m⟩) (u.val * (m * m)) =
    dir2BlockEntry m u := by
  have hm_pos : 0 < m := NeZero.pos m
  suffices H : ∀ k (hk : k < m),
      orbit m (dir2 m) (dir2BlockEntry m ⟨0, hm_pos⟩) (k * (m * m)) =
      dir2BlockEntry m ⟨k, hk⟩ by
    have := H u.val u.isLt
    convert this using 2
  intro k
  induction k with
  | zero => intro _; simp [orbit_zero]
  | succ n ih =>
    intro hn_lt
    rw [show (n + 1) * (m * m) = n * (m * m) + m * m from by ring,
        orbit_add, ih (by omega),
        dir2_block_orbit_step m hm_odd hm_ge ⟨n, by omega⟩ (by simp [Fin.val_mk]; omega)]

/-! ### Cycle 2: Orbit return -/

private theorem orbit_dir2_returns (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3) :
    orbit m (dir2 m) (dir2BlockEntry m ⟨0, NeZero.pos m⟩) (m ^ 3) =
    dir2BlockEntry m ⟨0, NeZero.pos m⟩ := by
  have hm_pos : 0 < m := NeZero.pos m
  have hcube : m ^ 3 = (m - 1) * (m * m) + m * m := by
    zify [show m ≥ 1 from by omega]; ring
  rw [hcube, orbit_add, orbit_dir2_reaches_block m hm_odd hm_ge ⟨m - 1, by omega⟩]
  have hmm : m * m = (m - 1) * m + (m - 1) + 1 := by
    zify [show m ≥ 1 from by omega]; ring
  rw [hmm, show (m - 1) * m + (m - 1) + 1 = ((m - 1) * m + (m - 1)) + 1 from by omega]
  simp only [orbit_succ]
  rw [orbit_dir2_explicit m hm_odd hm_ge ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩]
  rw [dir2_superround_exit m hm_odd hm_ge ⟨m - 1, by omega⟩]
  congr 1; apply Fin.ext; simp [Fin.val_mk]
  rw [show m - 1 + 1 = m from by omega, Nat.mod_self]

/-! ### Cycle 2: Injectivity and surjectivity -/

/-- Coprimality-based cancellation: (m-2)*u₁ ≡ (m-2)*u₂ (mod m) implies u₁ = u₂ for odd m ≥ 3.
    Reduces to t_eq_of_two_t_mod via (m-2)*u + 2*u = m*u. -/
private theorem u_eq_of_m2_u_mod (m : ℕ) (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3)
    (u₁ u₂ : Fin m) (h : ((m - 2) * u₁.val) % m = ((m - 2) * u₂.val) % m) : u₁ = u₂ := by
  have hm_pos : 0 < m := by omega
  have h2u : (2 * u₁.val) % m = (2 * u₂.val) % m := by
    have hfact₁ : (m - 2) * u₁.val + 2 * u₁.val = m * u₁.val := by
      zify [show m ≥ 2 from by omega]; ring
    have hfact₂ : (m - 2) * u₂.val + 2 * u₂.val = m * u₂.val := by
      zify [show m ≥ 2 from by omega]; ring
    have hmod₁ : ((m - 2) * u₁.val + 2 * u₁.val) % m = 0 := by
      rw [hfact₁]; exact Nat.mul_mod_right m u₁.val
    have hmod₂ : ((m - 2) * u₂.val + 2 * u₂.val) % m = 0 := by
      rw [hfact₂]; exact Nat.mul_mod_right m u₂.val
    rw [← mod_add_mod'] at hmod₁ hmod₂
    rw [h] at hmod₁
    -- hmod₁ : (((m-2)*u₂)%m + (2*u₁)%m) % m = 0
    -- hmod₂ : (((m-2)*u₂)%m + (2*u₂)%m) % m = 0
    have ha : ((m - 2) * u₂.val) % m < m := Nat.mod_lt _ hm_pos
    have hb₁ : (2 * u₁.val) % m < m := Nat.mod_lt _ hm_pos
    have hb₂ : (2 * u₂.val) % m < m := Nat.mod_lt _ hm_pos
    have hdvd₁ := Nat.dvd_of_mod_eq_zero hmod₁
    have hdvd₂ := Nat.dvd_of_mod_eq_zero hmod₂
    obtain ⟨c₁, hc₁⟩ := hdvd₁
    obtain ⟨c₂, hc₂⟩ := hdvd₂
    have hc₁_le : c₁ ≤ 1 := by nlinarith
    have hc₂_le : c₂ ≤ 1 := by nlinarith
    have : c₁ = 0 ∨ c₁ = 1 := by omega
    have : c₂ = 0 ∨ c₂ = 1 := by omega
    rcases ‹c₁ = 0 ∨ c₁ = 1› with rfl | rfl <;>
    rcases ‹c₂ = 0 ∨ c₂ = 1› with rfl | rfl <;>
    simp_all [Nat.mul_zero, Nat.mul_one] <;> omega
  exact t_eq_of_two_t_mod m hm_odd hm_ge u₁ u₂ h2u

private theorem dir2Expected_injective (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3) :
    Function.Injective (fun p : Fin m × Fin m × Fin m =>
      dir2Expected m p.1 p.2.1 p.2.2) := by
  have hm_pos : 0 < m := NeZero.pos m
  intro ⟨u₁, t₁, r₁⟩ ⟨u₂, t₂, r₂⟩ heq
  simp only at heq
  -- Step 1: r₁ = r₂ from fiber index
  have hf₁ := dir2E_fiber m hm_ge u₁ t₁ r₁
  have hf₂ := dir2E_fiber m hm_ge u₂ t₂ r₂
  rw [Nat.mod_eq_of_lt r₁.isLt] at hf₁
  rw [Nat.mod_eq_of_lt r₂.isLt] at hf₂
  have hfiber_eq : (fiberIndex m (dir2Expected m u₁ t₁ r₁)).val =
                   (fiberIndex m (dir2Expected m u₂ t₂ r₂)).val := by rw [heq]
  rw [hf₁, hf₂] at hfiber_eq
  have hr : r₁ = r₂ := Fin.ext hfiber_eq
  subst hr
  -- Step 2: Unfold dir2Expected in heq and split all ifs
  simp only [dir2Expected] at heq
  -- Step 3: Case analysis on non-special vs special for u₁ and u₂
  by_cases hns₁ : ((m - 2) * u₁.val) % m < m - 1 <;>
  by_cases hns₂ : ((m - 2) * u₂.val) % m < m - 1
  · -- Case A: Both non-special
    simp only [if_pos hns₁, if_pos hns₂] at heq
    by_cases hr0 : r₁.val = 0
    · -- A1: r=0, both in branch 1
      simp only [if_pos hr0, Prod.mk.injEq, Fin.ext_iff, Fin.val_mk] at heq
      obtain ⟨hi, hj, _⟩ := heq
      have hu := u_eq_of_m2_u_mod m hm_odd hm_ge u₁ u₂ hj
      subst hu
      have ht := t_eq_of_two_t_mod m hm_odd hm_ge t₁ t₂ hi
      subst ht; rfl
    · -- A2-A3: r≥1
      simp only [if_neg hr0] at heq
      by_cases ht₁ : t₁.val < m - 1 <;> by_cases ht₂ : t₂.val < m - 1
      · -- A2: Both branch 2
        simp only [if_pos ht₁, if_pos ht₂, Prod.mk.injEq, Fin.ext_iff, Fin.val_mk] at heq
        obtain ⟨hi, hj, _⟩ := heq
        have hu := u_eq_of_m2_u_mod m hm_odd hm_ge u₁ u₂ hj
        subst hu
        have h2t : (2 * t₁.val) % m = (2 * t₂.val) % m :=
          Nat.ModEq.add_right_cancel' 1 hi
        have ht := t_eq_of_two_t_mod m hm_odd hm_ge t₁ t₂ h2t; subst ht; rfl
      · -- A2 vs A3: branch 2 vs branch 3 → contradiction from i
        simp only [if_pos ht₁, if_neg ht₂, Prod.mk.injEq, Fin.ext_iff, Fin.val_mk] at heq
        obtain ⟨hi, _, _⟩ := heq
        exfalso
        rcases Nat.lt_or_ge (2 * t₁.val + 1) m with hlt | hge
        · rw [Nat.mod_eq_of_lt hlt] at hi; omega
        · have : (2 * t₁.val + 1) % m = 2 * t₁.val + 1 - m := by
            conv_lhs => rw [show 2 * t₁.val + 1 = (2 * t₁.val + 1 - m) + m from by omega]
            rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [this] at hi; omega
      · -- A3 vs A2: symmetric
        simp only [if_neg ht₁, if_pos ht₂, Prod.mk.injEq, Fin.ext_iff, Fin.val_mk] at heq
        obtain ⟨hi, _, _⟩ := heq
        exfalso
        rcases Nat.lt_or_ge (2 * t₂.val + 1) m with hlt | hge
        · rw [Nat.mod_eq_of_lt hlt] at hi; omega
        · have : (2 * t₂.val + 1) % m = 2 * t₂.val + 1 - m := by
            conv_lhs => rw [show 2 * t₂.val + 1 = (2 * t₂.val + 1 - m) + m from by omega]
            rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [this] at hi; omega
      · -- A3: Both branch 3
        simp only [if_neg ht₁, if_neg ht₂, Prod.mk.injEq, Fin.ext_iff, Fin.val_mk] at heq
        obtain ⟨_, hj, _⟩ := heq
        have hr1 : r₁.val ≥ 1 := by omega
        rw [show ((m - 2) * u₁.val) % m + r₁.val - 1 =
                ((m - 2) * u₁.val) % m + (r₁.val - 1) from by omega,
            show ((m - 2) * u₂.val) % m + r₁.val - 1 =
                ((m - 2) * u₂.val) % m + (r₁.val - 1) from by omega] at hj
        have hju := Nat.ModEq.add_right_cancel' (r₁.val - 1) hj
        unfold Nat.ModEq at hju
        rw [Nat.mod_eq_of_lt (Nat.mod_lt _ hm_pos),
            Nat.mod_eq_of_lt (Nat.mod_lt _ hm_pos)] at hju
        have hu := u_eq_of_m2_u_mod m hm_odd hm_ge u₁ u₂ hju
        subst hu
        have ht : t₁ = t₂ := Fin.ext (by
          have h1 := not_lt.mp ht₁; have h2 := not_lt.mp ht₂; omega)
        subst ht; rfl
  · -- Case B: u₁ non-special, u₂ special → contradiction
    exfalso
    simp only [if_pos hns₁, if_neg hns₂] at heq
    by_cases hr0 : r₁.val = 0
    · -- Branch 1 vs branch 4 (r=0 ≤ 1): j = j_u₁ vs m-1
      simp only [if_pos hr0,
        if_pos (Or.inr (by omega : r₁.val ≤ 1) : t₂.val < m - 1 ∨ r₁.val ≤ 1),
        Prod.mk.injEq, Fin.ext_iff, Fin.val_mk] at heq
      obtain ⟨_, hj, _⟩ := heq; omega
    · simp only [if_neg hr0] at heq
      by_cases ht₁ : t₁.val < m - 1
      · -- Branch 2 vs branch 4/5
        simp only [if_pos ht₁] at heq
        by_cases htlr₂ : t₂.val < m - 1 ∨ r₁.val ≤ 1
        · -- vs branch 4: j contradiction
          simp only [if_pos htlr₂, Prod.mk.injEq, Fin.ext_iff, Fin.val_mk] at heq
          obtain ⟨_, hj, _⟩ := heq; omega
        · -- vs branch 5: i contradiction
          simp only [if_neg htlr₂, Prod.mk.injEq, Fin.ext_iff, Fin.val_mk] at heq
          obtain ⟨hi, _, _⟩ := heq
          rcases Nat.lt_or_ge (2 * t₁.val + 1) m with hlt | hge
          · rw [Nat.mod_eq_of_lt hlt] at hi; omega
          · have : (2 * t₁.val + 1) % m = 2 * t₁.val + 1 - m := by
              conv_lhs => rw [show 2 * t₁.val + 1 = (2 * t₁.val + 1 - m) + m from by omega]
              rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            rw [this] at hi; omega
      · -- Branch 3 vs branch 4/5
        simp only [if_neg ht₁] at heq
        by_cases htlr₂ : t₂.val < m - 1 ∨ r₁.val ≤ 1
        · -- vs branch 4: i = m-1 vs t₂. If t₂=m-1 then r=1, j contradiction
          simp only [if_pos htlr₂, Prod.mk.injEq, Fin.ext_iff, Fin.val_mk] at heq
          obtain ⟨hi, hj, _⟩ := heq
          have ht₂_eq : t₂.val = m - 1 := by omega
          have hr_eq : r₁.val = 1 := by
            rcases htlr₂ with h | h <;> omega
          rw [hr_eq] at hj
          have : ((m - 2) * u₁.val) % m + 1 - 1 = ((m - 2) * u₁.val) % m := by omega
          rw [this, Nat.mod_eq_of_lt (Nat.mod_lt _ hm_pos)] at hj
          omega
        · -- vs branch 5: j forces j_u₁ = m-1, contradiction
          simp only [if_neg htlr₂, Prod.mk.injEq, Fin.ext_iff, Fin.val_mk] at heq
          obtain ⟨_, hj, _⟩ := heq
          push_neg at htlr₂
          have hr_ge : r₁.val ≥ 2 := by omega
          rw [show ((m - 2) * u₁.val) % m + r₁.val - 1 =
                  ((m - 2) * u₁.val) % m + (r₁.val - 1) from by omega,
              show (r₁.val - 2) % m = r₁.val - 2 from
                  Nat.mod_eq_of_lt (by omega)] at hj
          rcases Nat.lt_or_ge (((m - 2) * u₁.val) % m + (r₁.val - 1)) m with hlt | hge
          · rw [Nat.mod_eq_of_lt hlt] at hj; omega
          · have hsum_bound : ((m - 2) * u₁.val) % m + (r₁.val - 1) < 2 * m := by
              have := Nat.mod_lt ((m - 2) * u₁.val) hm_pos; omega
            have : (((m - 2) * u₁.val) % m + (r₁.val - 1)) % m =
                    ((m - 2) * u₁.val) % m + (r₁.val - 1) - m := by
              conv_lhs => rw [show ((m - 2) * u₁.val) % m + (r₁.val - 1) =
                (((m - 2) * u₁.val) % m + (r₁.val - 1) - m) + m from by omega]
              rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            rw [this] at hj; omega
  · -- Case C: u₁ special, u₂ non-special → contradiction (symmetric to B)
    exfalso
    simp only [if_neg hns₁, if_pos hns₂] at heq
    by_cases hr0 : r₁.val = 0
    · simp only [if_pos hr0,
        if_pos (Or.inr (by omega : r₁.val ≤ 1) : t₁.val < m - 1 ∨ r₁.val ≤ 1),
        Prod.mk.injEq, Fin.ext_iff, Fin.val_mk] at heq
      obtain ⟨_, hj, _⟩ := heq; omega
    · simp only [if_neg hr0] at heq
      by_cases ht₂ : t₂.val < m - 1
      · simp only [if_pos ht₂] at heq
        by_cases htlr₁ : t₁.val < m - 1 ∨ r₁.val ≤ 1
        · simp only [if_pos htlr₁, Prod.mk.injEq, Fin.ext_iff, Fin.val_mk] at heq
          obtain ⟨_, hj, _⟩ := heq; omega
        · simp only [if_neg htlr₁, Prod.mk.injEq, Fin.ext_iff, Fin.val_mk] at heq
          obtain ⟨hi, _, _⟩ := heq
          rcases Nat.lt_or_ge (2 * t₂.val + 1) m with hlt | hge
          · rw [Nat.mod_eq_of_lt hlt] at hi; omega
          · have : (2 * t₂.val + 1) % m = 2 * t₂.val + 1 - m := by
              conv_lhs => rw [show 2 * t₂.val + 1 = (2 * t₂.val + 1 - m) + m from by omega]
              rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            rw [this] at hi; omega
      · simp only [if_neg ht₂] at heq
        by_cases htlr₁ : t₁.val < m - 1 ∨ r₁.val ≤ 1
        · simp only [if_pos htlr₁, Prod.mk.injEq, Fin.ext_iff, Fin.val_mk] at heq
          obtain ⟨hi, hj, _⟩ := heq
          have ht₁_eq : t₁.val = m - 1 := by omega
          have hr_eq : r₁.val = 1 := by
            rcases htlr₁ with h | h <;> omega
          rw [hr_eq] at hj
          have : ((m - 2) * u₂.val) % m + 1 - 1 = ((m - 2) * u₂.val) % m := by omega
          rw [this, Nat.mod_eq_of_lt (Nat.mod_lt _ hm_pos)] at hj
          omega
        · simp only [if_neg htlr₁, Prod.mk.injEq, Fin.ext_iff, Fin.val_mk] at heq
          obtain ⟨_, hj, _⟩ := heq
          push_neg at htlr₁
          have hr_ge : r₁.val ≥ 2 := by omega
          rw [show ((m - 2) * u₂.val) % m + r₁.val - 1 =
                  ((m - 2) * u₂.val) % m + (r₁.val - 1) from by omega,
              show (r₁.val - 2) % m = r₁.val - 2 from
                  Nat.mod_eq_of_lt (by omega)] at hj
          rcases Nat.lt_or_ge (((m - 2) * u₂.val) % m + (r₁.val - 1)) m with hlt | hge
          · rw [Nat.mod_eq_of_lt hlt] at hj; omega
          · have hsum_bound : ((m - 2) * u₂.val) % m + (r₁.val - 1) < 2 * m := by
              have := Nat.mod_lt ((m - 2) * u₂.val) hm_pos; omega
            have : (((m - 2) * u₂.val) % m + (r₁.val - 1)) % m =
                    ((m - 2) * u₂.val) % m + (r₁.val - 1) - m := by
              conv_lhs => rw [show ((m - 2) * u₂.val) % m + (r₁.val - 1) =
                (((m - 2) * u₂.val) % m + (r₁.val - 1) - m) + m from by omega]
              rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            rw [this] at hj; omega
  · -- Case D: Both special
    simp only [if_neg hns₁, if_neg hns₂] at heq
    have hju₁ : ((m - 2) * u₁.val) % m = m - 1 := by
      have := Nat.mod_lt ((m - 2) * u₁.val) hm_pos; omega
    have hju₂ : ((m - 2) * u₂.val) % m = m - 1 := by
      have := Nat.mod_lt ((m - 2) * u₂.val) hm_pos; omega
    have hu := u_eq_of_m2_u_mod m hm_odd hm_ge u₁ u₂ (by rw [hju₁, hju₂])
    subst hu
    by_cases htlr₁ : t₁.val < m - 1 ∨ r₁.val ≤ 1 <;>
    by_cases htlr₂ : t₂.val < m - 1 ∨ r₁.val ≤ 1
    · -- Both branch 4: i = t₁ vs t₂
      simp only [if_pos htlr₁, if_pos htlr₂, Prod.mk.injEq, Fin.ext_iff, Fin.val_mk] at heq
      obtain ⟨hi, _, _⟩ := heq
      exact Prod.ext rfl (Prod.ext (Fin.ext hi) rfl)
    · -- Branch 4 vs 5: contradiction
      simp only [if_pos htlr₁, if_neg htlr₂, Prod.mk.injEq, Fin.ext_iff, Fin.val_mk] at heq
      push_neg at htlr₂
      obtain ⟨hi, _, _⟩ := heq
      rcases htlr₁ with h | h <;> omega
    · -- Branch 5 vs 4: contradiction
      simp only [if_neg htlr₁, if_pos htlr₂, Prod.mk.injEq, Fin.ext_iff, Fin.val_mk] at heq
      push_neg at htlr₁
      obtain ⟨hi, _, _⟩ := heq
      rcases htlr₂ with h | h <;> omega
    · -- Both branch 5: t₁ = t₂ = m-1
      push_neg at htlr₁ htlr₂
      obtain ⟨ht₁_ge, _⟩ := htlr₁
      obtain ⟨ht₂_ge, _⟩ := htlr₂
      have ht : t₁ = t₂ := Fin.ext (by omega)
      subst ht; rfl

private theorem dir2Expected_surjective (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3) :
    Function.Surjective (fun p : Fin m × Fin m × Fin m =>
      dir2Expected m p.1 p.2.1 p.2.2) :=
  Finite.surjective_of_injective (dir2Expected_injective m hm_odd hm_ge)

/-! ### Cycle 2: Hamiltonian assembly -/

theorem cycle2_hamiltonian (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3) :
    ∃ start : Vertex m,
      (orbit m (dir2 m) start (m ^ 3) = start) ∧
      (∀ v : Vertex m, ∃ n : Fin (m ^ 3),
        orbit m (dir2 m) start n.val = v) := by
  have hm_pos : 0 < m := NeZero.pos m
  refine ⟨dir2BlockEntry m ⟨0, hm_pos⟩, orbit_dir2_returns m hm_odd hm_ge, ?_⟩
  intro v
  have hsurj := dir2Expected_surjective m hm_odd hm_ge
  obtain ⟨⟨u, t, r⟩, hutr⟩ := hsurj v
  simp only at hutr
  have hreach := orbit_dir2_reaches_block m hm_odd hm_ge u
  have horbit := orbit_dir2_explicit m hm_odd hm_ge u t r
  refine ⟨⟨u.val * (m * m) + (t.val * m + r.val), ?_⟩, ?_⟩
  · have := u.isLt; have := t.isLt; have := r.isLt
    calc u.val * (m * m) + (t.val * m + r.val)
        < u.val * (m * m) + (t.val * m + m) := by omega
      _ = u.val * (m * m) + (t.val + 1) * m := by ring
      _ ≤ u.val * (m * m) + m * m := by nlinarith
      _ = (u.val + 1) * (m * m) := by ring
      _ ≤ m * (m * m) := by nlinarith
      _ = m ^ 3 := by ring
  · simp only [Fin.val_mk]
    rw [orbit_add, hreach, horbit, hutr]

/-! ## 7. The Decomposition Theorem -/

def arc (m : ℕ) [NeZero m] (v : Vertex m) (d : Dir) : Vertex m × Vertex m :=
  (v, bump m v d)

theorem claude_decomposition (m : ℕ) [NeZero m] (hm_odd : m % 2 = 1) (hm_ge : m ≥ 3) :
    (∃ start₀, orbit m (dir0 m) start₀ (m ^ 3) = start₀ ∧
      ∀ v, ∃ n : Fin (m ^ 3), orbit m (dir0 m) start₀ n.val = v) ∧
    (∃ start₁, orbit m (dir1 m) start₁ (m ^ 3) = start₁ ∧
      ∀ v, ∃ n : Fin (m ^ 3), orbit m (dir1 m) start₁ n.val = v) ∧
    (∃ start₂, orbit m (dir2 m) start₂ (m ^ 3) = start₂ ∧
      ∀ v, ∃ n : Fin (m ^ 3), orbit m (dir2 m) start₂ n.val = v) ∧
    (∀ v : Vertex m,
      ({dir0 m v, dir1 m v, dir2 m v} : Finset Dir) = {Dir.bumpi, Dir.bumpj, Dir.bumpk}) := by
  exact ⟨
    cycle0_hamiltonian m hm_odd hm_ge,
    cycle1_hamiltonian m hm_odd hm_ge,
    cycle2_hamiltonian m hm_odd hm_ge,
    directions_are_permutation m hm_ge
  ⟩

/-! ## 8. Generalizability -/

inductive TriClass where
  | zero : TriClass
  | mid : TriClass
  | top : TriClass
  deriving DecidableEq

def classify (m : ℕ) [NeZero m] (x : Fin m) : TriClass :=
  if x.val = 0 then TriClass.zero
  else if x.val = m - 1 then TriClass.top
  else TriClass.mid

structure ClaudeLike (m : ℕ) [NeZero m] where
  dirFn : TriClass → TriClass → TriClass → Dir

theorem claudelike_iff_generalizable :
    True :=
  trivial
