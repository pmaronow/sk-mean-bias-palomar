module
public import QuantitativePaper.VectorHeatCalculus
public import Targets.CascadeContinuityPi

@[expose] public section

/-! Genuine Gaussian-step continuity at zero variance. Domination is uniform
on each bounded variance interval and comes from the actual field Lipschitz
bound; no square-root differentiability at zero is required. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000

theorem continuousOn_vectorColeHopfStep_variance {n : ℕ} (f : Field n → ℝ)
    (K : ℝ≥0) (hf : LipschitzWith K f) (m : ℝ) (x : Field n) (a b : ℝ) :
    ContinuousOn (fun v => vectorColeHopfStep v m f x) (Icc a b) := by
  let A := fun v : ℝ => fun y : Fin n → ℝ => f (fieldShift v x (WithLp.toLp 2 y))
  have hAm (v : ℝ) : Measurable (A v) := by
    exact (hf.continuous.comp (by unfold fieldShift;fun_prop)).measurable
  have hA (v : ℝ) (hv : v∈Icc a b) (y : Fin n → ℝ) :
      |A v y| ≤ |f x|+((K : ℝ)*Real.sqrt b)*l1 y := by
    have h₁ := abs_fieldShift_lipschitz f K hf v x (WithLp.toLp 2 y)
    have h₂ := norm_toLp_le_l1 y
    have h₃ : Real.sqrt v ≤ Real.sqrt b := Real.sqrt_le_sqrt hv.2
    apply h₁.trans
    calc
      _ ≤ |f x|+(K : ℝ)*Real.sqrt v*l1 y :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left h₂ (mul_nonneg K.coe_nonneg (Real.sqrt_nonneg v)))
      _ ≤ _ := add_le_add le_rfl
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h₃ K.coe_nonneg) (l1_nonneg y))
  have hcont (y : Fin n → ℝ) : ContinuousOn (fun v => A v y) (Icc a b) := by
    exact (hf.continuous.comp (by unfold fieldShift;fun_prop)).continuousOn
  have hh := continuousOn_parisiStepPi_param (m := m) (v := 1)
    (C := |f x|) (D := (K : ℝ)*Real.sqrt b) (by positivity)
    (fun v _ => hAm v) hA hcont 0
  have he : (fun v => parisiStepPi n m 1 (A v) 0)=
      fun v => vectorColeHopfStep v m f x := by
    funext v
    unfold parisiStepPi vectorColeHopfStep
    have hshift : Continuous (fieldShift v x) := by unfold fieldShift;fun_prop
    split_ifs
    · rw [integral_fieldGaussian (fun z => f (fieldShift v x z)) (hf.continuous.comp hshift)]
      simp [A,Real.sqrt_one,Pi.add_def,Pi.smul_def]
    · unfold vectorStepPartition
      rw [integral_fieldGaussian (fun z => Real.exp (m*f (fieldShift v x z)))
        (Real.continuous_exp.comp (continuous_const.mul (hf.continuous.comp hshift)))]
      simp [A,Real.sqrt_one,Pi.add_def,Pi.smul_def,div_eq_mul_inv,mul_comm]
  rw [he] at hh
  exact hh

theorem continuous_vectorColeHopfStep_variance {n : ℕ} (f : Field n → ℝ)
    (K : ℝ≥0) (hf : LipschitzWith K f) (m : ℝ) (x : Field n) :
    Continuous (fun v => vectorColeHopfStep v m f x) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  exact (continuousOn_vectorColeHopfStep_variance f K hf m x (v-1) (v+1)).continuousAt
    (Icc_mem_nhds (by linarith) (by linarith))

end QuantitativePaper
