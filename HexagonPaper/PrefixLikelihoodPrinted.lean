module
public import HexagonPaper.PrefixLikelihoodAllProfiles
public import QuantitativeFollowup.SupportingPrintedScalarRootFreeDensity

@[expose] public section

/-! The exact printed prefix exponent, its normalization, and its root
value. Adding log 2 to the native potential cancels against the full
right-continuous prefix mass, including both endpoint atoms. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FRSB FourPapersCommon
open QuantitativeFollowup QuantitativePaper
open scoped NNReal ENNReal Topology BoundedContinuousFunction
namespace HexagonPaper
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def scalarPrintedPrefixDensity (β : ℝ) (μ : Paper.ParisiMeasure) (t : ℝ≥0)
    (sample : Paper.BrownianSample) : ℝ≥0∞ := ENNReal.ofReal (Real.exp
      (parisiCDF μ t*scalarPrintedPotential β μ t (β*canonicalBrownian t sample)-
        ∫q : Paper.Overlap,if (q:ℝ)≤t then
          scalarPrintedPotential β μ q (β*canonicalBrownian (q:ℝ).toNNReal sample) else 0
            ∂(μ : Measure Paper.Overlap)))

theorem scalarPrintedPrefixDensity_eq_native (β : ℝ) (μ : Paper.ParisiMeasure)
    (t : ℝ≥0) (sample : Paper.BrownianSample) :
    scalarPrintedPrefixDensity β μ t sample=forwardBrownianWeight β μ t sample := by
  let u := fun q : Paper.Overlap=>if (q:ℝ)≤t then (1:ℝ) else 0
  let v := fun q : Paper.Overlap=>if (q:ℝ)≤t then
    parisiPotential β μ (q,β*canonicalBrownian (q:ℝ).toNNReal sample) else 0
  have hu : Integrable u (μ : Measure Paper.Overlap) := by
    apply Integrable.of_bound
      ((measurable_const.ite (measurableSet_le measurable_subtype_coe measurable_const)
        measurable_const).aestronglyMeasurable) 1
    exact .of_forall fun q=>by dsimp [u];split_ifs <;> norm_num
  have hv : Integrable v (μ : Measure Paper.Overlap) := by
    apply Integrable.of_bound
      ((((continuous_parisiPotential β μ).comp
        (continuous_subtype_val.prodMk (((continuous_canonicalBrownian sample).comp
          (continuous_real_toNNReal.comp continuous_subtype_val)).const_mul β))).measurable).ite
          (measurableSet_le measurable_subtype_coe measurable_const) measurable_const).aestronglyMeasurable
      (β^2+|β| *‖canonicalBrownianPath sample‖)
    exact .of_forall fun q=>by
      dsimp [v]
      split_ifs
      · exact scalarBrownianPotential_bound β μ sample q
      · rw [abs_zero]
        positivity
  have he : (fun q : Paper.Overlap=>if (q:ℝ)≤t then
      scalarPrintedPotential β μ q (β*canonicalBrownian (q:ℝ).toNNReal sample) else 0)=
        (fun q=>Real.log 2*u q+v q) := by
    funext q
    dsimp [scalarPrintedPotential,u,v]
    split_ifs <;> ring
  have hc : (∫q,u q ∂(μ : Measure Paper.Overlap))=parisiCDF μ t :=
    (parisiCDF_eq_integral_upperIndicator μ t).symm
  unfold scalarPrintedPrefixDensity forwardBrownianWeight
  rw [he,integral_add (hu.const_mul _) hv,integral_const_mul,hc]
  unfold scalarPrintedPotential
  change ENNReal.ofReal (Real.exp (_-(_+forwardBrownianAction β μ t sample)))=_
  congr 2
  ring

/-- The source prefix law in its printed log(2 cosh) convention. -/
theorem scalarStoppedPath_printed_likelihood (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (t : ℝ≥0) (ht : (t:ℝ)≤1) :
    canonicalBrownianMeasure.map (scalarStoppedStatePath β μ t)=
      (canonicalBrownianMeasure.withDensity (scalarPrintedPrefixDensity β μ t)).map
        (scalarStoppedBrownianPath β t) := by
  have he : scalarPrintedPrefixDensity β μ t=forwardBrownianWeight β μ t :=
    funext (scalarPrintedPrefixDensity_eq_native β μ t)
  rw [he]
  exact scalarStoppedPath_likelihood β hβ μ t ht

theorem integral_scalarPrefixLikelihood_eq_one (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (t : ℝ≥0) (ht : (t:ℝ)≤1) :
    (∫sample,scalarPrefixLikelihood β μ t sample ∂canonicalBrownianMeasure)=1 := by
  have h := congrArg (fun P : Measure C(Paper.Overlap,ℝ)=>∫p,(1:ℝ) ∂P)
    (scalarStoppedPath_likelihood β hβ μ t ht)
  rw [integral_map_of_stronglyMeasurable (measurable_scalarStoppedStatePath β hβ μ t ht)
    stronglyMeasurable_const] at h
  have hi := integral_scalarStoppedBrownianPath_withDensity β μ t
    (1 : C(Paper.Overlap,ℝ)→ᵇℝ)
  simp only [BoundedContinuousFunction.coe_one,Pi.one_apply,mul_one] at hi
  rw [hi] at h
  simpa only [integral_const,probReal_univ,one_smul] using h.symm

theorem scalarPrefixLikelihood_zero (β : ℝ) (μ : Paper.ParisiMeasure)
    (sample : Paper.BrownianSample) : scalarPrefixLikelihood β μ 0 sample=1 := by
  have h := scalarPrefixLikelihood_stoppedAction β μ zeroOverlap sample
  have hz (q : Paper.Overlap) : scalarStoppedLevel zeroOverlap q=zeroOverlap := by
    apply Subtype.ext
    exact min_eq_right q.property.1
  have hi : (fun q=>scalarStoppedBrownianPotential β μ zeroOverlap sample q)=
      (fun _ : Paper.Overlap=>parisiPotential β μ (0,0)) := by
    funext q
    change parisiPotential β μ (scalarStoppedLevel zeroOverlap q,
      β*canonicalBrownian (scalarStoppedLevel zeroOverlap q : ℝ).toNNReal sample)=_
    rw [hz]
    change parisiPotential β μ (0,β*canonicalBrownian (0:ℝ).toNNReal sample)=_
    simp only [Real.toNNReal_zero,canonicalBrownian_zero,mul_zero]
  rw [hi,integral_const] at h
  simp only [zeroOverlap,Real.toNNReal_zero,canonicalBrownian_zero,mul_zero] at h
  simpa only [probReal_univ,one_smul,sub_self,Real.exp_zero] using h

theorem scalarPrintedPrefixDensity_zero (β : ℝ) (μ : Paper.ParisiMeasure)
    (sample : Paper.BrownianSample) : scalarPrintedPrefixDensity β μ 0 sample=1 := by
  rw [scalarPrintedPrefixDensity_eq_native]
  change ENNReal.ofReal (scalarPrefixLikelihood β μ 0 sample)=1
  rw [scalarPrefixLikelihood_zero]
  exact ENNReal.ofReal_one

end HexagonPaper
