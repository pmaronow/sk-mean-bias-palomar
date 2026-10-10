module
public import HexagonPaper.CavityFixedRowMixtureBasic
public import FourPapersCommon.FiniteJointLaw

@[expose] public section

/-! Genuine relative root density under a deterministic coupling shift.
The normalizers are actual Gaussian exponential integrals. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
variable {S I : Type} [Fintype S] [Fintype I]

theorem cavityGaussianRootStep_density (U : FiniteStateField S → ℝ)
    {C : NNReal} (hU : LipschitzWith C U) (a : ℝ)
    (R : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (H : FiniteStateField S) :
    finiteStateGaussianStepLaw a R U H =
      (finiteStateGaussianRawKernel R H).withDensity
        (fun Q => ENNReal.ofReal (Real.exp (a * U Q) / cavityGaussianRootNormalizer U a R H)) := by
  unfold finiteStateGaussianStepLaw Measure.tilted
  have hZ : (∫ Q, Real.exp (a * U Q) ∂finiteStateGaussianRawKernel R H) =
      cavityGaussianRootNormalizer U a R H := by
    rw [finiteStateGaussianRawKernel_apply, integral_map (by fun_prop)
      ((hU.continuous.measurable.const_mul a).exp.aestronglyMeasurable)]
    rfl
  rw [hZ]

theorem cavityGaussianRoot_relative_density (U : FiniteStateField S → ℝ)
    {C : NNReal} (hU : LipschitzWith C U) (a : ℝ)
    (R : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (H : FiniteStateField S) :
    finiteStateGaussianStepLaw a R U H =
      ((finiteStateGaussianStepLaw a R U 0).withDensity
        (fun Q => ENNReal.ofReal (Real.exp (a * (U (Q + H) - U Q)) *
          cavityGaussianRootNormalizer U a R 0 / cavityGaussianRootNormalizer U a R H))).map
        (fun Q => Q + H) := by
  have hZ0 := cavityGaussianRootNormalizer_pos U hU a R 0
  have hZH := cavityGaussianRootNormalizer_pos U hU a R H
  let f := fun Q => ENNReal.ofReal (Real.exp (a * U Q) / cavityGaussianRootNormalizer U a R 0)
  let w := fun Q => ENNReal.ofReal (Real.exp (a * (U (Q + H) - U Q)) *
    cavityGaussianRootNormalizer U a R 0 / cavityGaussianRootNormalizer U a R H)
  let v := fun Q => ENNReal.ofReal (Real.exp (a * U Q) / cavityGaussianRootNormalizer U a R H)
  have hf : Measurable f := ((hU.continuous.measurable.const_mul a).exp.div_const _).ennreal_ofReal
  have hw : Measurable w := by
    exact (((((hU.continuous.measurable.comp (measurable_id.add_const H)).sub
      hU.continuous.measurable).const_mul a).exp.mul_const _).div_const _).ennreal_ofReal
  have hv : Measurable v := ((hU.continuous.measurable.const_mul a).exp.div_const _).ennreal_ofReal
  have hraw : finiteStateGaussianRawKernel R H =
      (finiteStateGaussianRawKernel R 0).map (fun Q => Q + H) := by
    rw [finiteStateGaussianRawKernel_apply, finiteStateGaussianRawKernel_apply,
      Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext g
    simp only [zero_add, Function.comp_def]
    exact add_comm H (R g)
  have hfw : f * w = fun Q => v (Q + H) := by
    funext Q
    change ENNReal.ofReal _ * ENNReal.ofReal _ = ENNReal.ofReal _
    rw [←ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le hZ0.le)]
    congr 1
    have he : a * (U (Q + H) - U Q) = a * U (Q + H) - a * U Q := by ring
    rw [he, Real.exp_sub]
    field_simp [hZ0.ne', hZH.ne', (Real.exp_pos (a * U Q)).ne']
  rw [cavityGaussianRootStep_density U hU a R H,
    cavityGaussianRootStep_density U hU a R 0]
  change (finiteStateGaussianRawKernel R H).withDensity v =
    (((finiteStateGaussianRawKernel R 0).withDensity f).withDensity w).map (fun Q => Q + H)
  rw [←withDensity_mul _ hf hw, hfw,
    map_withDensity_pullback _ _ (by fun_prop) _ hv, hraw]

end HexagonPaper
