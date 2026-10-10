module
public import HexagonPaper.PrefixLikelihoodBounds
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import FRSB.PotentialMeasureContinuity

@[expose] public section

/-! Exact atom-preserving conversion of a prefix action into an integral of
a continuous stopped path. This form is weakly continuous even when the
profile charges the stopping level, although its CDF need not be. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FRSB FourPapersCommon
open scoped NNReal ENNReal Topology
namespace HexagonPaper
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def scalarStoppedLevel (t : Paper.Overlap) (q : Paper.Overlap) : Paper.Overlap :=
  ⟨min (q:ℝ) t,le_min q.property.1 t.property.1,(min_le_right _ _).trans t.property.2⟩

theorem continuous_scalarStoppedLevel (t : Paper.Overlap) :
    Continuous (scalarStoppedLevel t) :=
  (continuous_subtype_val.min continuous_const).subtype_mk _

theorem profile_stopped_integral_split (μ : Paper.ParisiMeasure)
    (t : Paper.Overlap) (f : C(Paper.Overlap,ℝ)) :
    (∫q,f (scalarStoppedLevel t q) ∂(μ : Measure Paper.Overlap))=
      (∫q,if (q:ℝ)≤t then f q else 0 ∂(μ : Measure Paper.Overlap))+
        (1-parisiCDF μ t)*f t := by
  have hf : Integrable (fun q : Paper.Overlap=>if (q:ℝ)≤t then f q else 0)
      (μ : Measure Paper.Overlap) := by
    apply Integrable.of_bound
      ((f.continuous.measurable.ite (measurableSet_le measurable_subtype_coe measurable_const)
        measurable_const).aestronglyMeasurable) ‖f‖
    exact .of_forall fun q=>by
      split_ifs
      · exact f.norm_coe_le_norm q
      · simpa only [norm_zero] using norm_nonneg f
  have hi : Integrable (fun q : Paper.Overlap=>(1-(if (q:ℝ)≤t then (1:ℝ) else 0))*f t)
      (μ : Measure Paper.Overlap) := by
    apply Integrable.of_bound
      (((measurable_const.sub (measurable_const.ite
        (measurableSet_le measurable_subtype_coe measurable_const) measurable_const)).mul
          measurable_const).aestronglyMeasurable) ‖f t‖
    exact .of_forall fun q=>by
      dsimp only [Pi.mul_apply,Pi.sub_apply]
      split_ifs <;> simp
  have he : (fun q=>f (scalarStoppedLevel t q))=
      (fun q : Paper.Overlap=>(if (q:ℝ)≤t then f q else 0)+
        (1-(if (q:ℝ)≤t then (1:ℝ) else 0))*f t) := by
    funext q
    by_cases hq : (q:ℝ)≤t
    · have hs : scalarStoppedLevel t q=q := by
        apply Subtype.ext;exact min_eq_left hq
      simp [hq,hs]
    · have hs : scalarStoppedLevel t q=t := by
        apply Subtype.ext;exact min_eq_right (not_le.mp hq).le
      simp [hq,hs]
  rw [he,integral_add hf hi,integral_mul_const,integral_sub (integrable_const _)]
  · rw [integral_const]
    have hc := parisiCDF_eq_integral_upperIndicator μ t
    rw [←hc]
    simp only [probReal_univ,one_smul]
  · exact Integrable.of_bound
      ((measurable_const.ite (measurableSet_le measurable_subtype_coe measurable_const)
        measurable_const).aestronglyMeasurable) 1
      (.of_forall fun q=>by split_ifs <;> norm_num)

def scalarStoppedBrownianPotential (β : ℝ) (μ : Paper.ParisiMeasure)
    (t : Paper.Overlap) (sample : Paper.BrownianSample) : C(Paper.Overlap,ℝ) :=
  ⟨fun q=>parisiPotential β μ (scalarStoppedLevel t q,
      β*canonicalBrownian (scalarStoppedLevel t q : ℝ).toNNReal sample),
    (continuous_parisiPotential β μ).comp
      (((continuous_subtype_val.comp (continuous_scalarStoppedLevel t))).prodMk
        ((((continuous_canonicalBrownian sample).comp
          (continuous_real_toNNReal.comp (continuous_subtype_val.comp
            (continuous_scalarStoppedLevel t))))).const_mul β))⟩

theorem scalarPrefixLikelihood_stoppedAction (β : ℝ) (μ : Paper.ParisiMeasure)
    (t : Paper.Overlap) (sample : Paper.BrownianSample) :
    scalarPrefixLikelihood β μ (t:ℝ).toNNReal sample=Real.exp
      (parisiPotential β μ (t,β*canonicalBrownian (t:ℝ).toNNReal sample)-
        ∫q,scalarStoppedBrownianPotential β μ t sample q ∂(μ : Measure Paper.Overlap)) := by
  let f : C(Paper.Overlap,ℝ) :=
    ⟨fun q=>parisiPotential β μ (q,β*canonicalBrownian (q:ℝ).toNNReal sample),
      (continuous_parisiPotential β μ).comp
        (continuous_subtype_val.prodMk
          (((continuous_canonicalBrownian sample).comp
            (continuous_real_toNNReal.comp continuous_subtype_val)).const_mul β))⟩
  have h := profile_stopped_integral_split μ t f
  change (∫q,scalarStoppedBrownianPotential β μ t sample q ∂(μ : Measure Paper.Overlap))=
    (∫q,if (q:ℝ)≤t then f q else 0 ∂(μ : Measure Paper.Overlap))+
      (1-parisiCDF μ t)*f t at h
  unfold scalarPrefixLikelihood forwardBrownianAction
  simp only [Real.coe_toNNReal _ t.property.1]
  rw [h]
  congr 1
  dsimp only [f,ContinuousMap.coe_mk]
  ring

end HexagonPaper
