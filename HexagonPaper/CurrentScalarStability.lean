module
public import QuantitativeFollowup.ScalarMinimizerStability
public import FRSB.MomentQuotient

@[expose] public section

/-! Current-paper bridges for the exact supremum-defined scalar stability
error and the positive minimum of the density-quotient denominator.
These strengthen the existing native stability-error convention without
changing any of the earlier theorem statements. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace HexagonPaper
open Paper FRSB QuantitativePaper QuantitativeFollowup FourPapersCommon
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- The exact error in current Proposition `prop:lz-stability`. -/
def currentScalarStabilityError (d : ℝ) (μ : Paper.ParisiMeasure) : ℝ :=
  max 0 (sSup (GammaPrime (Real.sqrt d) μ '' Icc (0 : ℝ) 1) - 1)

theorem currentScalarStabilityError_nonneg (d : ℝ) (μ : Paper.ParisiMeasure) :
    0 ≤ currentScalarStabilityError d μ :=
  le_max_left _ _

theorem currentScalarMultiplier_bddAbove (d : ℝ) (hd : 0 < d)
    (μ : Paper.ParisiMeasure) :
    BddAbove (GammaPrime (Real.sqrt d) μ '' Icc (0 : ℝ) 1) := by
  refine ⟨d, ?_⟩
  rintro x ⟨q, hq, rfl⟩
  simpa only [Real.sq_sqrt hd.le] using
    GammaPrime_le_beta_sq (Real.sqrt d) (Real.sqrt_pos.mpr hd).ne' μ hq

theorem currentScalarMultiplier_le_exact_error (d : ℝ) (hd : 0 < d)
    (μ : Paper.ParisiMeasure) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) :
    GammaPrime (Real.sqrt d) μ q ≤ 1 + currentScalarStabilityError d μ := by
  have hs := le_csSup (currentScalarMultiplier_bddAbove d hd μ)
    (show GammaPrime (Real.sqrt d) μ q ∈
      GammaPrime (Real.sqrt d) μ '' Icc (0 : ℝ) 1 from ⟨q, hq, rfl⟩)
  have he : sSup (GammaPrime (Real.sqrt d) μ '' Icc (0 : ℝ) 1) - 1 ≤
      currentScalarStabilityError d μ := le_max_right _ _
  linarith

/-- Pointwise continuity and the reference multiplier, rather than an
operator bound alone, give comparison with the old native error. -/
theorem currentScalarStabilityError_le_native (β : ℝ) (hβ : 1 < β)
    (μ : Paper.ParisiMeasure) (d : ℝ) (hd : d ∈ Icc (β^2 / 2) (β^2)) :
    currentScalarStabilityError d μ ≤ scalarOperatorStabilityError β μ d := by
  have hb : 0 < β := zero_lt_one.trans hβ
  have hdp : 0 < d := (half_pos (sq_pos_of_ne_zero hb.ne')).trans_le hd.1
  have hp : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdp
  obtain ⟨q0, hq0, hsupp, hunit, hdecay, href⟩ :=
    scalar_reference_multiplier β hβ (parisiMinimizer β 0)
      (isParisiMinimizer_selected β 0)
  have hpoint (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) :
      GammaPrime (Real.sqrt d) μ q ≤ 1 + scalarOperatorStabilityError β μ d := by
    have hdiff := GammaPrime_parameter_window_bound β (Real.sqrt d) β hb hp hb
      (by simpa only [Real.sq_sqrt hdp.le] using hd)
      ⟨by nlinarith [sq_nonneg β], le_rfl⟩ μ (parisiMinimizer β 0) q hq
    simp only [Real.sq_sqrt hdp.le, Real.norm_eq_abs] at hdiff
    have hle := (le_abs_self
      (GammaPrime (Real.sqrt d) μ q - GammaPrime β (parisiMinimizer β 0) q)).trans hdiff
    have ht := href q hq
    change GammaPrime (Real.sqrt d) μ q - GammaPrime β (parisiMinimizer β 0) q ≤
      scalarOperatorStabilityError β μ d at hle
    linarith
  have hs : sSup (GammaPrime (Real.sqrt d) μ '' Icc (0 : ℝ) 1) ≤
      1 + scalarOperatorStabilityError β μ d := by
    apply csSup_le (Set.image_nonempty.mpr (nonempty_Icc.mpr zero_le_one))
    rintro x ⟨q, hq, rfl⟩
    exact hpoint q hq
  exact max_le (scalarOperatorStabilityError_nonneg β hb μ d) (by linarith)

/-- The response order uses the exact current-paper error on the
minimizer's own endpoint-fixed transport space. -/
theorem currentScalarResponse_le_exact_error (β : ℝ) (hβ : 0 < β)
    (μ : Paper.ParisiMeasure) (d : ℝ) (hd : d ∈ Icc (β^2 / 2) (β^2))
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (hμ : μ ∈ scalarFloor s)
    (f : endpointFixedL2 (parisiFreeMeasure μ s)) :
    inner ℝ f (scalarResponseL2Operator (Real.sqrt d)
      (Real.sqrt_pos.mpr ((half_pos (sq_pos_of_ne_zero hβ.ne')).trans_le hd.1)).ne'
        μ s hs hμ f) ≤ (1 + currentScalarStabilityError d μ) * ‖f‖^2 := by
  have hdp : 0 < d := (half_pos (sq_pos_of_ne_zero hβ.ne')).trans_le hd.1
  have hp : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdp
  let ν := parisiFreeMeasure μ s
  let κ := scalarGammaMultiplierCoefficient (Real.sqrt d) hp.ne' μ
  let E := currentScalarStabilityError d μ
  have hpoint (q : Paper.Overlap) : κ q ≤ 1 + E :=
    currentScalarMultiplier_le_exact_error d hdp μ q q.property
  have hfsq : Integrable (fun q : Paper.Overlap => (f.val q)^2) ν :=
    (Lp.memLp f.val).integrable_sq
  have hik : Integrable (fun q : Paper.Overlap => κ q * (f.val q)^2) ν := by
    exact hfsq.bdd_mul κ.continuous.measurable.aestronglyMeasurable
      (.of_forall (scalarGammaMultiplierCoefficient_norm_le (Real.sqrt d) hp.ne' μ))
  have hnorm : (∫ q : Paper.Overlap, (f.val q)^2 ∂ν) = ‖f‖^2 := by
    rw [←real_inner_self_eq_norm_sq]
    change (∫ q : Paper.Overlap, (f.val q)^2 ∂ν) =
      ∫ q : Paper.Overlap, inner ℝ (f.val q) (f.val q) ∂ν
    apply integral_congr_ae
    exact .of_forall fun q => by simp
  have hi := integral_mono hik (hfsq.const_mul (1 + E))
    (fun q => mul_le_mul_of_nonneg_right (hpoint q) (sq_nonneg _))
  rw [integral_const_mul, hnorm] at hi
  exact (scalarResponseL2Operator_quadratic_domination
    (Real.sqrt d) hp μ s hs hμ f).trans hi

/-- The current density proof's positive compact minimum is attained.
`quotientDenominator` is the actual expectation E[C_q^3]. -/
theorem currentScalarXi_positive_minimum (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) :
    ∃ q0 ∈ Icc (0 : ℝ) 1, 0 < quotientDenominator β μ q0 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
        quotientDenominator β μ q0 ≤ quotientDenominator β μ q := by
  obtain ⟨q0, hq0, hmin⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_isMinOn
    (nonempty_Icc.mpr zero_le_one) (continuousOn_quotientDenominator β hβ μ)
  exact ⟨q0, hq0, quotientDenominator_pos β hβ μ q0 hq0, hmin⟩

end HexagonPaper
