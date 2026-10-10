module
public import QuantitativePaper.VectorFiniteGradientResponse
public import QuantitativePaper.VectorFiniteTailGradient

@[expose] public section

/-! Actual dimension-only finite-cell gradient and derivative bounds. -/
noncomputable section
open MeasureTheory Set FourPapersCommon
open scoped NNReal ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorFiniteTailGradient_eq_cell (s : RSBScheme k) (β t : ℝ)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (i : ℕ) (hi : i≤k+1)
    (hq : (q : ℝ)∈Icc (s.q i) (s.q (i+1))) :
    vectorFiniteTailGradient s β t q p=gradient (vectorFiniteCellPotential s β t p i q) := by
  unfold vectorFiniteTailGradient
  rw [vectorTailRecursion_eq_finiteCell s β t q p i hi hq]

theorem norm_vectorFiniteCellGradient_le (s : RSBScheme k) (β t : ℝ)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (i : ℕ) (hi : i≤k+1)
    (hq : (q : ℝ)∈Icc (s.q i) (s.q (i+1))) (x : Field n) :
    ‖gradient (vectorFiniteCellPotential s β t p i q) x‖≤Real.sqrt (n : ℝ) := by
  rw [←vectorFiniteTailGradient_eq_cell s β t q p i hi hq]
  exact norm_vectorFiniteTailGradient_le s β t q p x

theorem abs_vectorFiniteCellGradient_component_le (s : RSBScheme k) (β t : ℝ)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (i : ℕ) (hi : i≤k+1)
    (hq : (q : ℝ)∈Icc (s.q i) (s.q (i+1))) (x : Field n) (l : Fin n) :
    |gradient (vectorFiniteCellPotential s β t p i q) x l|≤1 := by
  rw [←vectorFiniteTailGradient_eq_cell s β t q p i hi hq,
    vectorFiniteTailGradient_eq_magnetization]
  exact vectorMagnetization_component_bound _ β t p _ x l

theorem vectorFiniteCellGradient_lipschitz (s : RSBScheme k) (β t : ℝ)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (i : ℕ) (hi : i≤k+1)
    (hq : (q : ℝ)∈Icc (s.q i) (s.q (i+1))) :
    LipschitzWith (n : ℝ≥0) (gradient (vectorFiniteCellPotential s β t p i q)) := by
  rw [←vectorFiniteTailGradient_eq_cell s β t q p i hi hq]
  exact vectorFiniteTailGradient_lipschitz s β t q p

theorem norm_fderiv_vectorFiniteCellGradient_component_le (s : RSBScheme k) (β t : ℝ)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (i : ℕ) (hi : i≤k+1)
    (hq : (q : ℝ)∈Icc (s.q i) (s.q (i+1))) (x : Field n) (l : Fin n) :
    ‖fderiv ℝ (fun y=>gradient (vectorFiniteCellPotential s β t p i q) y l) x‖≤(n : ℝ) := by
  have hh : LipschitzWith (n : ℝ≥0)
      (fun y=>gradient (vectorFiniteCellPotential s β t p i q) y l) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    exact (PiLp.dist_apply_le _ _ l).trans
      ((vectorFiniteCellGradient_lipschitz s β t q p i hi hq).dist_le_mul y z)
  simpa only [NNReal.coe_natCast] using norm_fderiv_le_of_lipschitz ℝ (x₀:=x) hh

end QuantitativePaper
