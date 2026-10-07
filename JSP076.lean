/-
  JSP-000076: How sparse can a set be if every two-coloring represents every
  sufficiently large integer as a sum of distinct same-colored elements?
  Improve the growth bounds.

  Reference: [BuEr85] Sárközy-Erdős 1985; [CFP21] Cilleruelo-Goldstern-Mata
  arXiv:2104.14766.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

namespace JSP076

open Finset

/-- A 2-coloring of ℕ: red (true) / blue (false). -/
abbrev TwoColor := ℕ → Bool

/-- Set of integers representable as a sum of distinct red elements of A. -/
noncomputable def redSumset (A : Finset ℕ) (χ : TwoColor) : Set ℕ :=
  { n : ℕ | ∃ S ⊆ A, S.Nonempty ∧ (∀ a ∈ S, χ a = true) ∧ n = ∑ a ∈ S, a }

/-- Similarly blue sumset. -/
noncomputable def blueSumset (A : Finset ℕ) (χ : TwoColor) : Set ℕ :=
  { n : ℕ | ∃ S ⊆ A, S.Nonempty ∧ (∀ a ∈ S, χ a = false) ∧ n = ∑ a ∈ S, a }

/-- A set A is **2-color complete** if for every 2-coloring, every
    sufficiently large integer is representable in either red or blue. -/
def TwoColorComplete (A : Finset ℕ) : Prop :=
  ∀ χ : TwoColor, ∀ᶠ n in Filter.atTop, n ∈ redSumset A χ ∨ n ∈ blueSumset A χ

/-- "Sparse set" predicate: |A ∩ [1, N]| ≤ N^{1/2 + ε} for some small ε. -/
def IsSparse (A : Finset ℕ) (ε : ℝ) : Prop :=
  ∀ᶠ N in Filter.atTop,
    ((A ∩ Finset.range (N + 1)).card : ℝ) ≤ Real.rpow ((N + 1 : ℕ) : ℝ) ((1 : ℝ) / 2 + ε)

/-- The result [CFP21] establishes: any 2-color complete set A must satisfy
    |A ∩ [1, N]| ≥ c · N^{1/2} for infinitely many N. -/
theorem cilleruelo_goldstern_mata_2021 (A : Finset ℕ) :
    TwoColorComplete A →
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ N in Filter.atTop,
      (c : ℝ) * Real.rpow ((N + 1 : ℕ) : ℝ) ((1 : ℝ) / 2) ≤ ((A ∩ Finset.range (N + 1)).card : ℝ) := by
  sorry

/-- JSP-000076: sparsest Rado sets grow at least N^{1/2}. -/
theorem jsp_000076 (A : Finset ℕ) (hSparse : IsSparse A ((1 : ℝ) / 4)) :
    ¬ TwoColorComplete A := by
  intro hComplete
  obtain ⟨c, hc, h⟩ := cilleruelo_goldstern_mata_2021 A hComplete
  sorry

end JSP076
