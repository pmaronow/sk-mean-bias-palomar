module
public import FRSB.BridgePathWeight
public import FourPapersCommon.WienerExponential

@[expose] public section

/-! Uniform Gaussian domination of the actual arbitrary-profile prefix
likelihood, including endpoint and initial atoms. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FRSB FourPapersCommon
open scoped NNReal ENNReal Topology
namespace HexagonPaper
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def scalarPrefixLikelihood (β : ℝ) (μ : Paper.ParisiMeasure) (t : ℝ≥0)
    (sample : Paper.BrownianSample) : ℝ :=
  Real.exp (parisiCDF μ t*parisiPotential β μ (t,β*canonicalBrownian t sample)-
    forwardBrownianAction β μ t sample)

@[simp] theorem forwardBrownianWeight_toReal (β : ℝ) (μ : Paper.ParisiMeasure)
    (t : ℝ≥0) (sample : Paper.BrownianSample) :
    (forwardBrownianWeight β μ t sample).toReal=scalarPrefixLikelihood β μ t sample :=
  ENNReal.toReal_ofReal (Real.exp_pos _).le

theorem measurable_forwardBrownianAction (β : ℝ) (μ : Paper.ParisiMeasure) (t : ℝ≥0) :
    Measurable (forwardBrownianAction β μ t) := by
  have hm := (continuous_forwardPathAction β μ (t:ℝ)).measurable.comp
    ((measurable_scaledBrownianPath β).comp measurable_canonicalBrownianPath)
  convert hm using 1
  funext sample
  unfold forwardBrownianAction forwardPathAction scaledBrownianPath
  rfl

theorem measurable_scalarPrefixLikelihood (β : ℝ) (μ : Paper.ParisiMeasure) (t : ℝ≥0) :
    Measurable (scalarPrefixLikelihood β μ t) := by
  exact ((((continuous_parisiPotential β μ).measurable.comp
    (measurable_const.prodMk ((measurable_canonicalBrownian t).const_mul β))).const_mul
      (parisiCDF μ t)).sub (measurable_forwardBrownianAction β μ t)).exp

theorem scalarBrownianPotential_bound (β : ℝ) (μ : Paper.ParisiMeasure)
    (sample : Paper.BrownianSample) (q : Paper.Overlap) :
    ‖parisiPotential β μ (q,β*canonicalBrownian (q:ℝ).toNNReal sample)‖ ≤
      β^2+|β| *‖canonicalBrownianPath sample‖ := by
  have h := parisiPotential_absolute_growth β μ q
    (β*canonicalBrownian (q:ℝ).toNNReal sample) q.property
  rw [Real.norm_eq_abs]
  apply h.trans
  apply add_le_add le_rfl
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [canonicalBrownianPath,ContinuousMap.coe_mk,Real.norm_eq_abs] using
      (canonicalBrownianPath sample).norm_coe_le_norm q) (abs_nonneg β)

theorem norm_forwardBrownianAction_le (β : ℝ) (μ : Paper.ParisiMeasure)
    (t : ℝ≥0) (sample : Paper.BrownianSample) :
    ‖forwardBrownianAction β μ t sample‖≤β^2+|β| *‖canonicalBrownianPath sample‖ := by
  unfold forwardBrownianAction
  have h := norm_integral_le_of_norm_le_const (μ:=(μ : Measure Paper.Overlap))
    (f:=fun q : Paper.Overlap=>if (q:ℝ)≤t then
      parisiPotential β μ (q,β*canonicalBrownian (q:ℝ).toNNReal sample) else 0)
    (.of_forall fun q=>by
      split_ifs
      · exact scalarBrownianPotential_bound β μ sample q
      · simp only [norm_zero];positivity)
  simpa only [probReal_univ,mul_one] using h

theorem scalarPrefixLikelihood_envelope (β : ℝ) (μ : Paper.ParisiMeasure)
    (t : ℝ≥0) (ht : (t:ℝ)≤1) (sample : Paper.BrownianSample) :
    ‖scalarPrefixLikelihood β μ t sample‖≤
      Real.exp (2*β^2+2*|β| *‖canonicalBrownianPath sample‖) := by
  rw [scalarPrefixLikelihood,Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  have hp := scalarBrownianPotential_bound β μ sample
    (⟨t,t.coe_nonneg,ht⟩ : Paper.Overlap)
  have hc : parisiCDF μ t ∈ Icc (0:ℝ) 1 := ⟨parisiCDF_nonneg μ t,parisiCDF_le_one μ t⟩
  have hB : canonicalBrownian (t:ℝ).toNNReal sample=canonicalBrownian t sample := by
    simp only [Real.toNNReal_coe]
  simp only [hB,Real.norm_eq_abs] at hp
  have ha := norm_forwardBrownianAction_le β μ t sample
  rw [Real.norm_eq_abs] at ha
  have hmul : parisiCDF μ t*parisiPotential β μ (t,β*canonicalBrownian t sample) ≤
      β^2+|β| *‖canonicalBrownianPath sample‖ := by
    calc
      _ ≤ parisiCDF μ t*|parisiPotential β μ (t,β*canonicalBrownian t sample)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hc.1
      _ ≤ 1*(β^2+|β| *‖canonicalBrownianPath sample‖) :=
        mul_le_mul hc.2 hp (abs_nonneg _) (by positivity)
      _ = _ := one_mul _
  nlinarith [(abs_le.mp ha).1]

theorem integrable_scalarPrefixLikelihood (β : ℝ) (μ : Paper.ParisiMeasure)
    (t : ℝ≥0) (ht : (t:ℝ)≤1) :
    Integrable (scalarPrefixLikelihood β μ t) canonicalBrownianMeasure := by
  have hi := (integrable_exp_norm_canonicalBrownianPath (2*|β|)).const_mul (Real.exp (2*β^2))
  apply hi.mono' (measurable_scalarPrefixLikelihood β μ t).aestronglyMeasurable
  exact .of_forall fun sample=>by
    rw [←Real.exp_add]
    exact scalarPrefixLikelihood_envelope β μ t ht sample

end HexagonPaper
