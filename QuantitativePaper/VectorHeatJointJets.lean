module
public import QuantitativePaper.VectorHeatSpatial

@[expose] public section

/-! Genuine joint variance/field continuity of the Gaussian heat value and
its first two spatial derivatives. Exponential growth of the actual input
jets supplies all local domination, including variance zero. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
open FourPapersCommon
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
variable {n : ℕ}

theorem continuous_iteratedFDeriv_vectorGaussianHeat {F : Field n → ℝ}
    (d : VectorHeatDatum F) (j : ℕ) (hj : j ≤ 2) :
    Continuous (fun p : ℝ×Field n=>iteratedFDeriv ℝ j (vectorGaussianHeat F p.1) p.2) := by
  simp_rw [iteratedFDeriv_vectorGaussianHeat d _ j hj _]
  apply continuous_iff_continuousAt.mpr
  intro p
  let B := fun z : Field n=>d.growthBound*Real.exp (d.rate*(‖p.2‖+1))*
    Real.exp ((d.rate*Real.sqrt (p.1+1))*‖z‖)
  have hjc := d.regularity.continuous_iteratedFDeriv (by exact_mod_cast hj)
  have hshift (z : Field n) : Continuous (fun w : ℝ×Field n=>fieldShift w.1 w.2 z) := by
    unfold fieldShift
    fun_prop
  apply continuousAt_of_dominated (bound := B)
  · exact Eventually.of_forall fun w=>(hjc.comp (by unfold fieldShift;fun_prop)).aestronglyMeasurable
  · have hv : ∀ᶠ w : ℝ×Field n in 𝓝 p,w.1<p.1+1 :=
      continuous_fst.continuousAt.eventually (Iio_mem_nhds (by linarith))
    have hx : ∀ᶠ w : ℝ×Field n in 𝓝 p,dist w.2 p.2<1 :=
      continuous_snd.continuousAt.eventually (Metric.ball_mem_nhds p.2 (by norm_num))
    filter_upwards [hv,hx] with w hw hwx
    exact Eventually.of_forall fun z=>by
      have hn : ‖w.2‖ ≤ ‖p.2‖+1 := by
        have hh := norm_add_le p.2 (w.2-p.2)
        rw [add_sub_cancel] at hh
        rw [dist_eq_norm] at hwx
        exact hh.trans (add_le_add (le_refl _) hwx.le)
      have hs : ‖fieldShift w.1 w.2 z‖ ≤ ‖p.2‖+1+Real.sqrt (p.1+1)*‖z‖ := by
        have hh := norm_add_le w.2 (Real.sqrt w.1 • z)
        simp only [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hh
        exact hh.trans (add_le_add hn (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hw.le) (norm_nonneg _)))
      apply (d.jet_bound j hj _).trans
      have hh := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs d.rate.coe_nonneg)) d.growthBound.coe_nonneg
      simpa only [B,mul_add,Real.exp_add,mul_assoc] using hh
  · exact (SYK.integrable_exp_mul_norm (ι := Fin n) (d.rate*Real.sqrt (p.1+1))).const_mul _
  · exact Eventually.of_forall fun z=>(hjc.comp (hshift z)).continuousAt

theorem continuous_fderiv_vectorGaussianHeat {F : Field n → ℝ}
    (d : VectorHeatDatum F) :
    Continuous (fun p : ℝ×Field n=>fderiv ℝ (vectorGaussianHeat F p.1) p.2) := by
  let A := (continuousMultilinearCurryFin1 ℝ (Field n) ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have he : (fun p : ℝ×Field n=>fderiv ℝ (vectorGaussianHeat F p.1) p.2)=
      (fun p=>A (iteratedFDeriv ℝ 1 (vectorGaussianHeat F p.1) p.2)) := by
    funext p
    ext w
    change _=(continuousMultilinearCurryFin1 ℝ (Field n) ℝ)
      (iteratedFDeriv ℝ 1 (vectorGaussianHeat F p.1) p.2) w
    rw [continuousMultilinearCurryFin1_apply,iteratedFDeriv_one_apply]
    simp
  rw [he]
  exact A.continuous.comp (continuous_iteratedFDeriv_vectorGaussianHeat d 1 (by omega))

theorem continuous_vectorHessian_vectorGaussianHeat {F : Field n → ℝ}
    (d : VectorHeatDatum F) :
    Continuous (fun p : ℝ×Field n=>vectorHessian (vectorGaussianHeat F p.1) p.2) := by
  simp_rw [vectorHessian_eq_bilinearOfTwo]
  exact (vectorBilinearOfTwoCLM n).continuous.comp
    (continuous_iteratedFDeriv_vectorGaussianHeat d 2 le_rfl)

end QuantitativePaper
