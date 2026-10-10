module
public import QuantitativePaper.VectorHeatCalculus
public import Targets.RSBMassPiSemigroup

@[expose] public section

/-! Actual Gaussian composition of vector Cole--Hopf cells, including zero
mass and zero variance. This is the identity needed for common refinements. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000

theorem guerraGrowth_vector_field {n : ℕ} (f : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) : GuerraGrowth (fun y => f (WithLp.toLp 2 y)) := by
  have hc : Continuous (fun y : Fin n → ℝ => WithLp.toLp 2 y) := by fun_prop
  refine ⟨(hf.continuous.comp hc).measurable,|f 0|,(K : ℝ),K.coe_nonneg,?_⟩
  intro y
  have hh := abs_fieldShift_lipschitz f K hf 1 0 (WithLp.toLp 2 y)
  simp only [fieldShift,Real.sqrt_one,one_smul,zero_add,mul_one] at hh
  exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (norm_toLp_le_l1 y) K.coe_nonneg))

theorem vectorColeHopfStep_semigroup {n : ℕ} (f : Field n → ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (m : ℝ) (hm : 0 ≤ m) (v w : ℝ)
    (hv : 0 ≤ v) (hw : 0 ≤ w) (x : Field n) :
    vectorColeHopfStep v m (vectorColeHopfStep w m f) x=
      vectorColeHopfStep (v+w) m f x := by
  rw [vectorColeHopfStep_eq_pi _ (vectorColeHopfStep_lipschitz f K hf w m hm).continuous,
    vectorColeHopfStep_eq_pi f hf.continuous]
  have he : (fun y : Fin n → ℝ => vectorColeHopfStep w m f (WithLp.toLp 2 y))=
      parisiStepPi n m w (fun y => f (WithLp.toLp 2 y)) := by
    funext y
    simpa only [WithLp.ofLp_toLp] using vectorColeHopfStep_eq_pi f hf.continuous w m (WithLp.toLp 2 y)
  rw [he]
  exact (congrFun (parisiStepPi_add m hv hw (guerraGrowth_vector_field f K hf)) x.ofLp).symm

end QuantitativePaper
