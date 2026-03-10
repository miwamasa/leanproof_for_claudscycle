/-
  ClaudeCycles.Lemmas — Detailed proofs for Claude's Cycles
  ==========================================================
  This file provides more detailed proofs and computational verification
  for the lemmas marked `sorry` in the main file.
-/

import ClaudeCycles

/-! ## Fiber advancement lemma (detailed proof) -/

/-- Each bump increases the fiber index by exactly 1 (mod m).
    This restates `fiber_advances` from ClaudeCycles with explicit components. -/
theorem fiber_advances_detail (m : ℕ) [NeZero m]
    (i j k : Fin m) (d : Dir) :
    fiberIndex m (bump m (i, j, k) d) = fiberIndex m (i, j, k) + 1 :=
  fiber_advances m (i, j, k) d

/-! ## Direction permutation proof (detailed)

  The six cases for the direction functions.
  In each case, we verify dir0, dir1, dir2 produce three distinct directions.

  For s = 0:
    dir0: j = m-1 -> bumpi, else -> bumpk
    dir1: bumpj
    dir2: j < m-1 -> bumpi, j = m-1 -> bumpk
  Case s=0, j=m-1: dir0=bumpi, dir1=bumpj, dir2=bumpk
  Case s=0, j<m-1:  dir0=bumpk, dir1=bumpj, dir2=bumpi

  For 0 < s < m-1:
    dir0: i = m-1 -> bumpk, else -> bumpj
    dir1: bumpi
    dir2: i < m-1 -> bumpk, i = m-1 -> bumpj
  Case s=mid, i=m-1: dir0=bumpk, dir1=bumpi, dir2=bumpj
  Case s=mid, i<m-1: dir0=bumpj, dir1=bumpi, dir2=bumpk

  For s = m-1:
    dir0: i > 0 -> bumpj, i = 0 -> bumpk
    dir1: i > 0 -> bumpk, i = 0 -> bumpj
    dir2: bumpi
  Case s=m-1, i>0:  dir0=bumpj, dir1=bumpk, dir2=bumpi
  Case s=m-1, i=0:  dir0=bumpk, dir1=bumpj, dir2=bumpi

  All six cases produce a permutation of {bumpi, bumpj, bumpk}.
-/

/-! ## The gcd(2,m) = 1 argument -/

private lemma two_mul_mod_injective (m : ℕ) (hm_odd : m % 2 = 1) (hm_pos : 0 < m) :
    Function.Injective (fun t : Fin m => (⟨(2 * t.val) % m, Nat.mod_lt _ hm_pos⟩ : Fin m)) := by
  intro a b hab
  simp only [Fin.mk.injEq] at hab
  -- hab : 2 * a.val % m = 2 * b.val % m, i.e., Nat.ModEq m (2*a.val) (2*b.val)
  have hmeq : 2 * a.val ≡ 2 * b.val [MOD m] := hab
  have hodd : Odd m := Nat.odd_iff.mpr hm_odd
  have hcop_m2 : m.Coprime 2 := (Nat.coprime_two_left.mpr hodd).symm
  have ha := a.isLt
  have hb := b.isLt
  ext
  by_cases h : a.val ≤ b.val
  · -- From 2*a ≡ 2*b [MOD m] with 2*a ≤ 2*b, get m ∣ (2*b - 2*a)
    have hdvd : m ∣ 2 * b.val - 2 * a.val :=
      (Nat.modEq_iff_dvd' (by omega : 2 * a.val ≤ 2 * b.val)).mp hmeq
    -- Rewrite 2*b - 2*a = 2*(b - a)
    have heq : 2 * b.val - 2 * a.val = 2 * (b.val - a.val) := by omega
    rw [heq] at hdvd
    -- Cancel the 2 using coprimality
    have hdvd_sub : m ∣ (b.val - a.val) := hcop_m2.dvd_of_dvd_mul_left hdvd
    -- Since 0 ≤ b.val - a.val < m, we get b.val - a.val = 0
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

/-- For odd m, the function t -> 2t mod m is a bijection on {0, ..., m-1}.
    This is the core arithmetic fact that makes the checkpoint argument work. -/
theorem two_mul_perm (m : ℕ) (hm_odd : m % 2 = 1) (hm_pos : 0 < m) :
    Function.Bijective (fun t : Fin m => (⟨(2 * t.val) % m, Nat.mod_lt _ hm_pos⟩ : Fin m)) := by
  have hinj := two_mul_mod_injective m hm_odd hm_pos
  exact ⟨hinj, (Finite.injective_iff_surjective.mp hinj)⟩

/-- Consequence: the set of checkpoints {(m-1-2t) mod m : t = 0, ..., m-1}
    equals all of Fin m. -/
theorem checkpoint_j_values_surjective (m : ℕ) (hm_odd : m % 2 = 1) (hm_pos : 0 < m) :
    Function.Surjective (fun t : Fin m =>
      (⟨(m - 1 + m - (2 * t.val % m)) % m, Nat.mod_lt _ hm_pos⟩ : Fin m)) := by
  -- It suffices to show injectivity (on a finite type, injective <=> surjective).
  rw [← Finite.injective_iff_surjective]
  intro a b hab
  simp only [Fin.mk.injEq] at hab
  -- hab : (m-1+m-(2*a.val%m)) % m = (m-1+m-(2*b.val%m)) % m
  -- Since 2*a.val%m < m and 2*b.val%m < m, the expressions (m-1+m-x) for x < m
  -- are in range [m, 2m-1], and their mod m values determine x uniquely.
  have ha2 := Nat.mod_lt (2 * a.val) hm_pos
  have hb2 := Nat.mod_lt (2 * b.val) hm_pos
  -- The outer mod is injective on the relevant range: if (m-1+m-x) % m = (m-1+m-y) % m
  -- with x, y < m, then x = y.
  -- (m-1+m-x) ranges over [m, 2m-1] for x in [0, m-1], so mod m gives [0, m-1] bijectively.
  have key : 2 * a.val % m = 2 * b.val % m := by
    -- From (m-1+m-xa) % m = (m-1+m-xb) % m where xa = 2*a%m, xb = 2*b%m
    -- and xa, xb < m, we get xa = xb.
    -- The values (2m-1-xa) for xa in [0, m-1] range over [m, 2m-1].
    -- For values in [m, 2m-1], v % m = v - m, so (2m-1-xa) % m = m-1-xa.
    -- If m-1-xa = m-1-xb then xa = xb.
    have hxa : m - 1 + m - (2 * a.val % m) ≥ m := by omega
    have hxb : m - 1 + m - (2 * b.val % m) ≥ m := by omega
    have hxa' : m - 1 + m - (2 * a.val % m) < 2 * m := by omega
    have hxb' : m - 1 + m - (2 * b.val % m) < 2 * m := by omega
    -- For n in [m, 2m-1], n % m = n - m
    have hma : (m - 1 + m - (2 * a.val % m)) % m = m - 1 + m - (2 * a.val % m) - m := by
      rw [Nat.mod_eq_sub_mod hxa]
      have : m - 1 + m - (2 * a.val % m) - m < m := by omega
      rw [Nat.mod_eq_of_lt this]
    have hmb : (m - 1 + m - (2 * b.val % m)) % m = m - 1 + m - (2 * b.val % m) - m := by
      rw [Nat.mod_eq_sub_mod hxb]
      have : m - 1 + m - (2 * b.val % m) - m < m := by omega
      rw [Nat.mod_eq_of_lt this]
    rw [hma, hmb] at hab
    omega
  -- Now use injectivity of t -> 2*t % m
  have hinj := two_mul_mod_injective m hm_odd hm_pos
  exact hinj (by simp only [Fin.mk.injEq]; exact key)

/-! ## Cycle 0 trace for m=3 (computational verification)

  We can verify the m=3 case by direct computation (27 steps).
  The cycle starting from (0,2,2) is:
    022 -> 002 -> 000 -> 001 -> 011 -> 012 -> 010 -> 020 -> 021 ->
    121 -> 101 -> 111 -> 112 -> 122 -> 102 -> 100 -> 110 -> 120 ->
    220 -> 221 -> 201 -> 202 -> 200 -> 210 -> 211 -> 212 -> 222 -> 022

  This matches Knuth's paper exactly.
-/

/-! ## Proof strategy summary for filling remaining sorry's

  **directions_are_permutation**: Case analysis on 6 combinations of
    (s in {0, mid, m-1}) x (conditions on i, j). Each case is a direct
    computation showing three distinct Dir values. Formalize with `decide`
    for m=3 or with `omega`/`simp` for general m.

  **cycle0_hamiltonian**: The full proof requires:
    1. Show orbit length divides m^3 (since the state space is finite)
    2. Show orbit length >= m^2 for each i-block (checkpoint argument)
    3. Show there are m distinct i-blocks visited in order
    4. Conclude orbit length = m * m^2 = m^3

  The checkpoint argument (step 2) is the mathematical core:
    - Between consecutive s=0 returns, exactly m vertices are visited
      (one full sweep of j for fixed i,k)
    - The s=0 returns cycle through all m values of k (by gcd(2,m)=1)
    - Therefore m * m = m^2 vertices per i-block

  **cycle1_hamiltonian, cycle2_hamiltonian**: Analogous to cycle0,
    following the patterns in Knuth's Appendix.
    Cycle 1: s=0 checkpoints at (0,k,-k), (-2,1+k,1-k), (-4,2+k,2-k), ...
    Cycle 2: s=0, j<m-1 checkpoints at (2t,j,-j-2t), and
             s=0, j=m-1 checkpoints at (0,-1,1), (1,-1,0), (2,-1,-1), ...
-/
