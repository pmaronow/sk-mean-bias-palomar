module
public import QuantitativeFollowup.ScalarMultiplierDomination
public import QuantitativeFollowup.ScalarMultiplierContinuity
public import QuantitativeFollowup.ScalarReferenceMultiplier

@[expose] public section

/-! A genuine Hilbert-space stability bound at the scalar reference
minimizer, with no supplied response-order premise. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace QuantitativeFollowup
open Paper FRSB QuantitativePaper FourPapersCommon
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def scalarOperatorStabilityError (β : ℝ) (μ : Paper.ParisiMeasure) (d : ℝ) : ℝ :=
  scalarMultiplierContinuityConstant β*(Paper.parisiCDFDistance μ (parisiMinimizer β 0)+|d-β^2|)

theorem scalarOperatorStabilityError_nonneg (β : ℝ) (hβ : 0 < β) (μ : Paper.ParisiMeasure) (d : ℝ) :
    0  ≤  scalarOperatorStabilityError β μ d :=
  mul_nonneg (scalarMultiplierContinuityConstant_pos β hβ).le (add_nonneg (Paper.parisiCDFDistance_nonneg _ _) (abs_nonneg _))

theorem scalar_reference_operator_stability (β : ℝ) (hβ : 1<β) (μ : Paper.ParisiMeasure)
    (d : ℝ) (hd : d∈Icc (β^2/2) (β^2)) (s : ℝ) (hs : s∈Icc (0:ℝ) 1)
    (hμ : μ∈scalarFloor s) (f : endpointFixedL2 (parisiFreeMeasure μ s)) :
    inner ℝ f (scalarResponseL2Operator (Real.sqrt d)
      (Real.sqrt_pos.mpr ((half_pos (sq_pos_of_ne_zero (zero_lt_one.trans hβ).ne')).trans_le hd.1)).ne' μ s hs hμ f)  ≤ 
      (1+scalarOperatorStabilityError β μ d)*‖f‖^2 := by
  have hb : 0 < β := zero_lt_one.trans hβ
  have hdp : 0<d := (half_pos (sq_pos_of_ne_zero hb.ne')).trans_le hd.1
  have hp : 0<Real.sqrt d := Real.sqrt_pos.mpr hdp
  let ν := parisiFreeMeasure μ s
  let κ := scalarGammaMultiplierCoefficient (Real.sqrt d) hp.ne' μ
  let E := scalarOperatorStabilityError β μ d
  obtain ⟨q0,hq0,hsupp,hunit,hdecay,href⟩:=scalar_reference_multiplier β hβ (parisiMinimizer β 0) (isParisiMinimizer_selected β 0)
  have hpoint (q : Paper.Overlap) : κ q  ≤  1+E := by
    have hdiff := GammaPrime_parameter_window_bound β (Real.sqrt d) β hb hp hb
      (by simpa only [Real.sq_sqrt hdp.le] using hd)
      ⟨by nlinarith [sq_nonneg β],le_rfl⟩ μ (parisiMinimizer β 0) q q.property
    simp only [Real.sq_sqrt hdp.le,Real.norm_eq_abs] at hdiff
    have ht := href q q.property
    have hle := (le_abs_self (GammaPrime (Real.sqrt d) μ q-GammaPrime β (parisiMinimizer β 0) q)).trans hdiff
    change GammaPrime (Real.sqrt d) μ q  ≤  1+E
    change GammaPrime (Real.sqrt d) μ q-GammaPrime β (parisiMinimizer β 0) q  ≤  E at hle
    linarith
  have hfsq : Integrable (fun q : Paper.Overlap=>(f.val q)^2) ν := (Lp.memLp f.val).integrable_sq
  have hik : Integrable (fun q : Paper.Overlap=>κ q*(f.val q)^2) ν := by
    exact hfsq.bdd_mul κ.continuous.measurable.aestronglyMeasurable
      (.of_forall (scalarGammaMultiplierCoefficient_norm_le (Real.sqrt d) hp.ne' μ))
  have hnorm : (∫q : Paper.Overlap,(f.val q)^2 ∂ν)=‖f‖^2 := by
    rw [←real_inner_self_eq_norm_sq]
    change (∫q : Paper.Overlap,(f.val q)^2 ∂ν)=∫q : Paper.Overlap,inner ℝ (f.val q) (f.val q) ∂ν
    apply integral_congr_ae
    exact .of_forall fun q=>by simp
  have hi := integral_mono hik (hfsq.const_mul (1+E)) (fun q=>mul_le_mul_of_nonneg_right (hpoint q) (sq_nonneg _))
  rw [integral_const_mul,hnorm] at hi
  exact (scalarResponseL2Operator_quadratic_domination (Real.sqrt d) hp μ s hs hμ f).trans hi

end QuantitativeFollowup
