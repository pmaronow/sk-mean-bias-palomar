module
public import FourPapersCommon.FiniteTriangleCutoff
public import FourPapersCommon.OneSidedGridCover
public import Mathlib.Topology.Algebra.Support

@[expose] public section

/-! The constructed triangular tests have genuine compact support inside
an open spatial interval. Nonemptiness of the selected cells gives a
nonzero test through its literal positive integral. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 1500000

theorem finiteTriangleCutoff_support_subset (S : Finset ℕ) (a : ℕ → ℝ) (ell : ℝ)
    (hell : 0 < ell) :
    Function.support (finiteTriangleCutoff S a ell) ⊆
      ⋃ i ∈ S, Icc (a i) (a i + ell) := by
  intro x hx
  by_contra h
  apply hx
  apply finiteTriangleCutoff_zero_outside S a ell hell
  intro hu
  obtain ⟨i, hi⟩ := mem_iUnion.mp hu
  obtain ⟨his, hxi⟩ := mem_iUnion.mp hi
  exact h (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨his, ⟨hxi.1.le, hxi.2.le⟩⟩⟩)

theorem finiteTriangleCutoff_tsupport_subset (S : Finset ℕ) (a : ℕ → ℝ) (ell : ℝ)
    (hell : 0 < ell) :
    tsupport (finiteTriangleCutoff S a ell) ⊆ ⋃ i ∈ S, Icc (a i) (a i + ell) := by
  apply (isClosed_biUnion_finset (fun _ _ => isClosed_Icc)).closure_subset_iff.mpr
  exact finiteTriangleCutoff_support_subset S a ell hell

theorem finiteTriangleCutoff_hasCompactSupport (S : Finset ℕ) (a : ℕ → ℝ) (ell : ℝ)
    (hell : 0 < ell) : HasCompactSupport (finiteTriangleCutoff S a ell) :=
  HasCompactSupport.of_support_subset_isCompact
    (S.isCompact_biUnion (fun _ _ => isCompact_Icc))
    (finiteTriangleCutoff_support_subset S a ell hell)

theorem finiteTriangleCutoff_tsupport_inside (S : Finset ℕ) (a : ℕ → ℝ) (ell q : ℝ)
    (hell : 0 < ell) (hinside : ∀ i ∈ S, Icc (a i) (a i + ell) ⊆ Ioo (0 : ℝ) q) :
    tsupport (finiteTriangleCutoff S a ell) ⊆ Ioo (0 : ℝ) q := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp (finiteTriangleCutoff_tsupport_subset S a ell hell hx)
  obtain ⟨his, hxi⟩ := mem_iUnion.mp hi
  exact hinside i his hxi

theorem finiteTriangleCutoff_nonzero (S : Finset ℕ) (a : ℕ → ℝ) (ell : ℝ)
    (hell : 0 < ell) (hS : S.Nonempty) (ha : ∀ i ∈ S, 0 ≤ a i)
    (he : ∀ i ∈ S, a i + ell ≤ 1) : finiteTriangleCutoff S a ell ≠ 0 := by
  intro hf
  have hv := finiteTriangleCutoff_integral_unit S a ell hell ha he
  rw [hf] at hv
  simp only [Pi.zero_apply, intervalIntegral.integral_zero] at hv
  have hcard : 0 < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hS
  have : 0 < (S.card : ℝ) * ell / 2 := by positivity
  linarith

/-- The positive predecessor construction supplies all support requirements
for the actual disjoint triangular test. -/
theorem positive_predecessor_cutoff_support (psi : ℝ → ℝ) (q L A : ℝ)
    (hL : 0 < L) (hA : 0 < A) (hroot : psi 0 ≤ 0)
    (hslope : ∀ z x : ℝ, 0 ≤ z → z ≤ x → x < q →
      psi x - psi z ≤ L * (x - z)) :
    let ell := A / (4 * L)
    let S := gridCellsMeeting q ell {x : ℝ | x ∈ Ioo (0 : ℝ) q ∧ A < psi x}
    HasCompactSupport (finiteTriangleCutoff S (fun i => ((i : ℝ) - 1) * ell) ell) ∧
      tsupport (finiteTriangleCutoff S (fun i => ((i : ℝ) - 1) * ell) ell) ⊆ Ioo (0 : ℝ) q := by
  dsimp only
  let ell := A / (4 * L)
  have hell : 0 < ell := div_pos hA (by positivity)
  refine ⟨finiteTriangleCutoff_hasCompactSupport _ _ _ hell, ?_⟩
  apply finiteTriangleCutoff_tsupport_inside _ _ _ _ hell
  intro i hi
  have hsub := (one_sided_positive_predecessors psi q L A hL hA hroot hslope i hi).2.1
  have he : ((i : ℝ)-1)*ell+ell = (i : ℝ)*ell := by ring
  change Icc (((i : ℝ)-1)*ell) (((i : ℝ)-1)*ell+ell) ⊆ Ioo (0 : ℝ) q
  rw [he]
  exact hsub

end FourPapersCommon
