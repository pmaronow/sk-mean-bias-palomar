module
public import FourPapersCommon.MonotoneFiniteBins
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic

@[expose] public section

/-! Actual predecessor and successor grid covers of level sets of a
function with a one-sided Lipschitz bound. These are the two interior
covering arguments in the isolation proof; the intervals are constructed,
and their measure and disjointness are proved. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open scoped ENNReal
namespace FourPapersCommon
set_option maxHeartbeats 1000000

def gridCellsMeeting (q ell : ℝ) (D : Set ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (Nat.ceil (q / ell) + 1)).filter fun i =>
    ∃ x ∈ D, x ∈ Ico ((i : ℝ) * ell) (((i : ℝ) + 1) * ell)

theorem gridCellsMeeting_witness (q ell : ℝ) (D : Set ℝ)
    {i : ℕ} (hi : i ∈ gridCellsMeeting q ell D) :
    ∃ x ∈ D, x ∈ Ico ((i : ℝ) * ell) (((i : ℝ) + 1) * ell) := by
  classical
  exact (Finset.mem_filter.mp (show i ∈ (Finset.range (Nat.ceil (q / ell) + 1)).filter
    (fun i : ℕ => ∃ x ∈ D, x ∈ Ico ((i : ℝ) * ell) (((i : ℝ) + 1) * ell)) from hi)).2

theorem gridCellsMeeting_cover (q ell : ℝ) (D : Set ℝ) (hell : 0 < ell)
    (hD : D ⊆ Icc (0 : ℝ) q) :
    D ⊆ ⋃ i ∈ gridCellsMeeting q ell D,
      Ico ((i : ℝ) * ell) (((i : ℝ) + 1) * ell) := by
  classical
  intro x hx
  let i : ℕ := Nat.floor (x / ell)
  have hlo := Nat.floor_le (div_nonneg (hD hx).1 hell.le)
  have hhi := Nat.lt_floor_add_one (x / ell)
  have hcell : x ∈ Ico ((i : ℝ) * ell) (((i : ℝ) + 1) * ell) := by
    constructor
    · exact (le_div_iff₀ hell).mp hlo
    · exact (div_lt_iff₀ hell).mp hhi
  have hi : i ∈ gridCellsMeeting q ell D := by
    unfold gridCellsMeeting
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, x, hx, hcell⟩
    exact Nat.lt_succ_of_le ((Nat.floor_mono
      (div_le_div_of_nonneg_right (hD hx).2 hell.le)).trans (Nat.floor_le_ceil _))
  exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hcell⟩⟩

theorem gridCellsMeeting_measure_bound (q ell : ℝ) (D : Set ℝ) (hell : 0 < ell)
    (hD : D ⊆ Icc (0 : ℝ) q) :
    volume.real D ≤ (gridCellsMeeting q ell D).card * ell := by
  classical
  have hsum : (∑ i ∈ gridCellsMeeting q ell D,
      volume (Ico ((i : ℝ) * ell) (((i : ℝ) + 1) * ell))) < ∞ := by
    apply ENNReal.sum_lt_top.mpr
    intro i hi
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_lt_top
  have hm := measureReal_mono (gridCellsMeeting_cover q ell D hell hD)
    (show volume (⋃ i ∈ gridCellsMeeting q ell D,
      Ico ((i : ℝ) * ell) (((i : ℝ) + 1) * ell)) ≠ ∞ from
        ((measure_biUnion_finset_le _ _).trans_lt hsum).ne)
  have hs := measureReal_biUnion_finset_le (μ := volume)
    (gridCellsMeeting q ell D) (fun i : ℕ =>
      Ico ((i : ℝ) * ell) (((i : ℝ) + 1) * ell))
  have hv (i : ℕ) : volume.real (Ico ((i : ℝ) * ell) (((i : ℝ) + 1) * ell)) = ell := by
    rw [Real.volume_real_Ico]
    ring_nf
    exact max_eq_left hell.le
  simp only [hv, Finset.sum_const, nsmul_eq_mul] at hs
  exact hm.trans hs

theorem shifted_grid_intervals_pairwiseDisjoint (ell c : ℝ) (hell : 0 < ell) :
    Pairwise (fun i j : ℕ => Disjoint
      (Ioo (((i : ℝ) + c) * ell) (((i : ℝ) + c + 1) * ell))
      (Ioo (((j : ℝ) + c) * ell) (((j : ℝ) + c + 1) * ell))) := by
  have hd (i j : ℕ) (hlt : i < j) : Disjoint
      (Ioo (((i : ℝ) + c) * ell) (((i : ℝ) + c + 1) * ell))
      (Ioo (((j : ℝ) + c) * ell) (((j : ℝ) + c + 1) * ell)) := by
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
    nlinarith [mul_le_mul_of_nonneg_right hcast hell.le, hxi.2, hxj.1]
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact hd i j hlt
  · exact (hd j i hlt).symm

theorem one_sided_positive_predecessors (psi : ℝ → ℝ) (q L A : ℝ)
    (hL : 0 < L) (hA : 0 < A) (hroot : psi 0 ≤ 0)
    (hslope : ∀ z x : ℝ, 0 ≤ z → z ≤ x → x < q →
      psi x - psi z ≤ L * (x - z)) :
    let ell := A / (4 * L)
    let D := {x : ℝ | x ∈ Ioo (0 : ℝ) q ∧ A < psi x}
    ∀ i ∈ gridCellsMeeting q ell D,
      4 ≤ i ∧ Icc (((i : ℝ) - 1) * ell) ((i : ℝ) * ell) ⊆ Ioo (0 : ℝ) q ∧
      ∀ z ∈ Icc (((i : ℝ) - 1) * ell) ((i : ℝ) * ell), A / 2 < psi z := by
  dsimp only
  let ell := A / (4 * L)
  have hell : 0 < ell := div_pos hA (by positivity)
  have hscale : 4 * L * ell = A := by dsimp [ell]; field_simp
  intro i hi
  obtain ⟨x, hx, hcell⟩ := gridCellsMeeting_witness q ell _ hi
  have hxroot := hslope 0 x le_rfl hx.1.1.le hx.1.2
  have hxlarge : 4 * ell < x := by
    apply (mul_lt_mul_iff_right₀ hL).mp
    nlinarith [hx.2]
  have hicast : 4 ≤ (i : ℝ) := by
    by_contra h
    have hiNat : i < 4 := by exact_mod_cast lt_of_not_ge h
    have hile : (i : ℝ) + 1 ≤ 4 := by exact_mod_cast Nat.succ_le_of_lt hiNat
    nlinarith [mul_le_mul_of_nonneg_right hile hell.le, hcell.2]
  have hiNat : 4 ≤ i := by exact_mod_cast hicast
  have hsub : Icc (((i : ℝ) - 1) * ell) ((i : ℝ) * ell) ⊆ Ioo (0 : ℝ) q := by
    intro z hz
    constructor
    · exact (mul_pos (by linarith : 0 < (i : ℝ) - 1) hell).trans_le hz.1
    · exact hz.2.trans_lt (hcell.1.trans_lt hx.1.2)
  refine ⟨hiNat, hsub, ?_⟩
  intro z hz
  have hz0 := (hsub hz).1
  have hzx : z ≤ x := hz.2.trans hcell.1
  have hxslope := hslope z x hz0.le hzx hx.1.2
  have hdist : x - z < 2 * ell := by linarith [hcell.2, hz.1]
  nlinarith [hx.2, mul_lt_mul_of_pos_left hdist hL]

theorem one_sided_negative_successors (psi : ℝ → ℝ) (q L A : ℝ)
    (hL : 0 < L) (hA : 0 < A)
    (hslope : ∀ z x : ℝ, 0 ≤ z → z ≤ x → x < q →
      psi x - psi z ≤ L * (x - z)) :
    let ell := A / (4 * L)
    let D := {x : ℝ | x ∈ Ioo (0 : ℝ) (q - 2 * ell) ∧ psi x < -A}
    ∀ i ∈ gridCellsMeeting q ell D,
      Icc (((i : ℝ) + 1) * ell) (((i : ℝ) + 2) * ell) ⊆ Ioo (0 : ℝ) q ∧
      ∀ z ∈ Icc (((i : ℝ) + 1) * ell) (((i : ℝ) + 2) * ell), psi z < -A / 2 := by
  dsimp only
  let ell := A / (4 * L)
  have hell : 0 < ell := div_pos hA (by positivity)
  have hscale : 4 * L * ell = A := by dsimp [ell]; field_simp
  intro i hi
  obtain ⟨x, hx, hcell⟩ := gridCellsMeeting_witness q ell _ hi
  have hsub : Icc (((i : ℝ) + 1) * ell) (((i : ℝ) + 2) * ell) ⊆ Ioo (0 : ℝ) q := by
    intro z hz
    constructor
    · have hpos : 0 < ((i : ℝ) + 1) * ell := mul_pos (by positivity) hell
      exact hpos.trans_le hz.1
    · linarith [hz.2, hcell.1, hx.1.2]
  refine ⟨hsub, ?_⟩
  intro z hz
  have hxz : x ≤ z := hcell.2.le.trans hz.1
  have hzslope := hslope x z hx.1.1.le hxz (hsub hz).2
  have hdist : z - x ≤ 2 * ell := by linarith [hz.2, hcell.1]
  nlinarith [hx.2, mul_le_mul_of_nonneg_left hdist hL.le]

end FourPapersCommon
