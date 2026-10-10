module
public import QuantitativePaper.VectorFiniteMild
public import QuantitativePaper.VectorMildLimit
public import FRSB.GridMeasureIdentification

@[expose] public section

/-! The actual arbitrary-measure vector mild equation. It is proved by
finite-cell Itô verification, an actual finite-grid telescope, and uniform
limits of the constructed potentials and genuine gradients. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000

theorem vectorTailRecursion_zero_diffusion {n k : ℕ} (s : RSBScheme k) (β t q : ℝ)
    (hc : (1-t)*β^2=0) (p : Couplings n×ℝ) (j : ℕ) :
    vectorTailRecursion s β t q p j=vectorTerminalPotential n β t p := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext x
    rw [vectorTailRecursion,ih]
    have hv : (1-t)*(β^2*(max q (s.q (k+2-j))-max q (s.q (k+1-j))))=0 := by
      rw [←mul_assoc,hc,zero_mul]
    rw [hv,vectorColeHopfStep_zero_variance]

theorem vectorMeasureTailPotential_zero_diffusion {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (hc : (1-t)*β^2=0) (q : Paper.Overlap)
    (p : Couplings n×ℝ) (x : Field n) :
    vectorMeasureTailPotential μ β t q p x=vectorTerminalPotential n β t p x := by
  have hh := tendsto_vectorDyadicTailPotential μ β t q ht q.property p x
  have he : (fun j => vectorDyadicTailPotential μ β t q j p x)=
      (fun _ : ℕ => vectorTerminalPotential n β t p x) := by
    funext j
    unfold vectorDyadicTailPotential
    rw [vectorTailRecursion_zero_diffusion _ β t q hc]
  rw [he] at hh
  exact (tendsto_nhds_unique hh tendsto_const_nhds)

theorem vectorMeasure_mild_equation_of_nonzero {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) :
    vectorMeasureTailPotential μ β t q p x=vectorTerminalHeat β t q p x+
      vectorMeasureMildCorrection μ β t q p x := by
  have hV := tendsto_vectorDyadicTailPotential μ β t q ht.le q.property p x
  have hC := (tendstoUniformly_vectorDyadicMildCorrection (n := n) μ β t ht.le).tendsto_at
    (q,(p,x))
  have hLim := (tendsto_const_nhds (x := vectorTerminalHeat β t q p x)).add hC
  have he (j : ℕ) : vectorDyadicTailPotential μ β t q j p x=
      vectorTerminalHeat β t q p x+vectorDyadicMildCorrection μ β t q j p x := by
    have hh := vectorFinite_mild_equation (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      β t hβ ht q p x
    rw [FRSB.parisiSchemeMeasure_grid_eq] at hh
    exact hh
  have hD : Tendsto (fun j => vectorDyadicTailPotential μ β t q j p x) atTop
      (𝓝 (vectorTerminalHeat β t q p x+vectorMeasureMildCorrection μ β t q p x)) := by
    simpa only [←he] using hLim
  exact tendsto_nhds_unique hV hD

theorem vectorMeasure_mild_equation {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) :
    vectorMeasureTailPotential μ β t q p x=vectorTerminalHeat β t q p x+
      vectorMeasureMildCorrection μ β t q p x := by
  by_cases hβ : β=0
  · rw [vectorMeasureTailPotential_zero_diffusion μ β t ht (by simp [hβ]) q p x]
    simp [vectorTerminalHeat,vectorMeasureMildCorrection,hβ,fieldShift]
  by_cases he : t=1
  · rw [vectorMeasureTailPotential_zero_diffusion μ β t ht (by simp [he]) q p x]
    simp [vectorTerminalHeat,vectorMeasureMildCorrection,he,fieldShift]
  exact vectorMeasure_mild_equation_of_nonzero μ β t hβ (lt_of_le_of_ne ht he) q p x

end QuantitativePaper
