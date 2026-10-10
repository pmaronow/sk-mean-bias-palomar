module
public import HexagonPaper.PrefixLikelihoodStoppedAction
public import HexagonPaper.PrefixLikelihoodFinitePath

@[expose] public section

/-! Weak-profile continuity of the actual prefix likelihood and the actual
stopped diffusion path. The proof uses the continuous stopped action and
therefore does not require CDF convergence at an atom. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FRSB FourPapersCommon
open scoped NNReal ENNReal Topology
namespace HexagonPaper
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem integrable_scalarStoppedBrownianPotential (β : ℝ) (μ ν : Paper.ParisiMeasure)
    (t : Paper.Overlap) (sample : Paper.BrownianSample) :
    Integrable (scalarStoppedBrownianPotential β μ t sample) (ν : Measure Paper.Overlap) :=
  Integrable.of_bound (scalarStoppedBrownianPotential β μ t sample).continuous.measurable.aestronglyMeasurable
    ‖scalarStoppedBrownianPotential β μ t sample‖
    (.of_forall fun q=>(scalarStoppedBrownianPotential β μ t sample).norm_coe_le_norm q)

theorem scalarStoppedBrownianPotential_measure_error (β : ℝ)
    (μ ν : Paper.ParisiMeasure) (t : Paper.Overlap) (sample : Paper.BrownianSample) :
    ‖(∫q,scalarStoppedBrownianPotential β ν t sample q ∂(ν : Measure Paper.Overlap))-
      ∫q,scalarStoppedBrownianPotential β μ t sample q ∂(ν : Measure Paper.Overlap)‖ ≤
        parisiPotentialMeasureError β ν μ := by
  rw [←integral_sub
    (integrable_scalarStoppedBrownianPotential β ν ν t sample)
    (integrable_scalarStoppedBrownianPotential β μ ν t sample)]
  have h := norm_integral_le_of_norm_le_const
    (μ:=(ν : Measure Paper.Overlap))
    (f:=fun q=>scalarStoppedBrownianPotential β ν t sample q-
      scalarStoppedBrownianPotential β μ t sample q)
    (.of_forall fun q=>parisiPotential_measure_error_bound β ν μ
      (scalarStoppedLevel t q)
      (β*canonicalBrownian (scalarStoppedLevel t q : ℝ).toNNReal sample)
        (scalarStoppedLevel t q).property)
  simpa only [probReal_univ,mul_one] using h

theorem tendsto_scalarStoppedBrownianAction_of_weak {A : Type*} {l : Filter A}
    [l.IsCountablyGenerated] (β : ℝ) (μ : Paper.ParisiMeasure) (ν : A→Paper.ParisiMeasure)
    (hν : Tendsto ν l (𝓝 μ)) (t : Paper.Overlap) (sample : Paper.BrownianSample) :
    Tendsto (fun i=>∫q,scalarStoppedBrownianPotential β (ν i) t sample q
      ∂(ν i : Measure Paper.Overlap)) l
        (𝓝 (∫q,scalarStoppedBrownianPotential β μ t sample q ∂(μ : Measure Paper.Overlap))) := by
  have hfixed := ((ProbabilityMeasure.continuous_integral_continuousMap
    (scalarStoppedBrownianPotential β μ t sample)).tendsto μ).comp hν
  have herr := tendsto_parisiPotentialMeasureError_of_weak β μ ν hν
  have hzero : Tendsto (fun i=>‖(∫q,scalarStoppedBrownianPotential β (ν i) t sample q
      ∂(ν i : Measure Paper.Overlap))-
      ∫q,scalarStoppedBrownianPotential β μ t sample q ∂(ν i : Measure Paper.Overlap)‖)
        l (𝓝 0) :=
    squeeze_zero (fun _=>norm_nonneg _)
      (fun i=>scalarStoppedBrownianPotential_measure_error β μ (ν i) t sample) herr
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hfixedzero := (hfixed.sub_const
    (∫q,scalarStoppedBrownianPotential β μ t sample q ∂(μ : Measure Paper.Overlap))).norm
  exact squeeze_zero (fun _=>norm_nonneg _)
    (fun i=>norm_sub_le_norm_sub_add_norm_sub _ _ _) (by simpa using hzero.add hfixedzero)

theorem tendsto_scalarPrefixLikelihood_of_weak {A : Type*} {l : Filter A}
    [l.IsCountablyGenerated] (β : ℝ) (μ : Paper.ParisiMeasure) (ν : A→Paper.ParisiMeasure)
    (hν : Tendsto ν l (𝓝 μ)) (t : ℝ≥0) (ht : (t:ℝ)≤1) (sample : Paper.BrownianSample) :
    Tendsto (fun i=>scalarPrefixLikelihood β (ν i) t sample) l
      (𝓝 (scalarPrefixLikelihood β μ t sample)) := by
  let q : Paper.Overlap := ⟨t,t.coe_nonneg,ht⟩
  have he (ρ : Paper.ParisiMeasure) := scalarPrefixLikelihood_stoppedAction β ρ q sample
  simp only [q,Real.toNNReal_coe] at he
  simp_rw [he]
  exact Real.continuous_exp.continuousAt.tendsto.comp
    ((tendsto_parisiPotential_of_weak β μ ν hν t
      (β*canonicalBrownian t sample) ⟨t.coe_nonneg,ht⟩).sub
        (tendsto_scalarStoppedBrownianAction_of_weak β μ ν hν q sample))

theorem tendsto_scalarStoppedStatePath_of_weak {A : Type*} {l : Filter A}
    [l.IsCountablyGenerated] (β : ℝ) (μ : Paper.ParisiMeasure) (ν : A→Paper.ParisiMeasure)
    (hν : Tendsto ν l (𝓝 μ)) (t : ℝ≥0) (ht : (t:ℝ)≤1) (sample : Paper.BrownianSample) :
    Tendsto (fun i=>scalarStoppedStatePath β (ν i) t sample) l
      (𝓝 (scalarStoppedStatePath β μ t sample)) := by
  rw [ContinuousMap.tendsto_iff_tendstoUniformly]
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [optimalState_uniform_convergence_of_weak β ν μ hν ε hε] with i hi q
  rw [dist_eq_norm,norm_sub_rev]
  exact hi sample (min (q:ℝ) t)
    ⟨le_min q.property.1 t.coe_nonneg,(min_le_right _ _).trans ht⟩

end HexagonPaper
