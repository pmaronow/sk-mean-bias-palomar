module
public import FourPapersCommon.MixedFiniteDiffusionLaw
public import FourPapersCommon.MixedMeasure
public import FRSB.GlobalMeasureStability

@[expose] public section

/-! The actual one-point magnetization law is jointly weakly continuous in
the overlap probability measure and physical evaluation time. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Real Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
namespace FourPapersCommon
set_option maxHeartbeats 1000000

def mixedMagnetization (ξ : AdmissibleEvenMixture) (h : ℝ) (μ : ParisiMeasure)
    (q : Overlap) (sample : BrownianSample) : ℝ :=
  mixedGradient ξ μ ((q : ℝ), mixedState ξ h μ sample q)

theorem measurable_mixedMagnetization (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : ParisiMeasure) (q : Overlap) : Measurable (mixedMagnetization ξ h μ q) := by
  change Measurable (fun sample => Paper.parisiGradient (mixedBeta ξ) (mixedMeasure ξ μ)
    (ξ.clock (q : ℝ), mixedState ξ h μ sample q))
  exact (Paper.continuous_parisiGradient _ _).measurable.comp
    (measurable_const.prodMk (measurable_mixedState ξ h μ q.property))

def mixedMagnetizationLaw (ξ : AdmissibleEvenMixture) (h : ℝ) (μ : ParisiMeasure)
    (q : Overlap) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map
    (⟨Paper.canonicalBrownianMeasure, inferInstance⟩ : ProbabilityMeasure BrownianSample)
    (mixedMagnetization ξ h μ q)

theorem tendsto_selectedStateReal_of_weak_and_time {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (β h : ℝ) (hβ : β ≠ 0)
    (μn : ι → ParisiMeasure) (μ : ParisiMeasure) (hμ : Tendsto μn L (𝓝 μ))
    (tn : ι → Overlap) (t : Overlap) (ht : Tendsto tn L (𝓝 t)) (ω : BrownianSample) :
    Tendsto (fun i => Paper.selectedParisiStateReal β h hβ (μn i) ω (tn i)) L
      (𝓝 (Paper.selectedParisiStateReal β h hβ μ ω t)) := by
  have hfixed := (Paper.continuous_selectedParisiStateReal β h hβ μ ω).continuousAt.tendsto.comp
    (continuous_subtype_val.continuousAt.tendsto.comp ht)
  have herror : Tendsto (fun i => Paper.selectedParisiStateReal β h hβ (μn i) ω (tn i) -
      Paper.selectedParisiStateReal β h hβ μ ω (tn i)) L (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero]
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [selectedState_uniform_convergence_of_weak β h hβ μn μ hμ ε hε] with i hi
    simpa only [dist_zero_right, norm_norm] using hi ω (tn i) (tn i).property
  simpa only [Function.comp_def, sub_add_cancel, zero_add] using herror.add hfixed

theorem tendsto_mixedMagnetization_of_weak_and_time {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μn : ι → ParisiMeasure) (μ : ParisiMeasure) (hμ : Tendsto μn L (𝓝 μ))
    (qn : ι → Overlap) (q : Overlap) (hq : Tendsto qn L (𝓝 q)) (ω : BrownianSample) :
    Tendsto (fun i => mixedMagnetization ξ h (μn i) (qn i) ω) L
      (𝓝 (mixedMagnetization ξ h μ q ω)) := by
  let β := mixedBeta ξ
  let ν := mixedMeasure ξ μ
  let νn := fun i => mixedMeasure ξ (μn i)
  have hν : Tendsto νn L (𝓝 ν) := (continuous_mixedMeasure ξ).continuousAt.tendsto.comp hμ
  have ht : Tendsto (fun i => ξ.unitClock (qn i)) L (𝓝 (ξ.unitClock q)) :=
    ξ.continuous_unitClock.continuousAt.tendsto.comp hq
  have hs := tendsto_selectedStateReal_of_weak_and_time β h (mixedBeta_ne_zero ξ)
    νn ν hν (fun i => ξ.unitClock (qn i)) (ξ.unitClock q) ht ω
  have hfixed := (Paper.continuous_parisiGradient β ν).continuousAt.tendsto.comp
    ((continuous_subtype_val.continuousAt.tendsto.comp ht).prodMk_nhds hs)
  have hgrad := ((FRSB.continuous_gradientBCF β).continuousAt.tendsto.comp hν).sub_const
    (Paper.parisiGradientBCF β ν)
  have hnorm : Tendsto (fun i => ‖Paper.parisiGradientBCF β (νn i) -
      Paper.parisiGradientBCF β ν‖) L (𝓝 0) := by simpa using hgrad.norm
  have he : Tendsto (fun i =>
      Paper.parisiGradient β (νn i) ((ξ.unitClock (qn i) : ℝ),
        Paper.selectedParisiStateReal β h (mixedBeta_ne_zero ξ) (νn i) ω (ξ.unitClock (qn i))) -
      Paper.parisiGradient β ν ((ξ.unitClock (qn i) : ℝ),
        Paper.selectedParisiStateReal β h (mixedBeta_ne_zero ξ) (νn i) ω (ξ.unitClock (qn i))))
      L (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero]
    exact squeeze_zero (fun _ => norm_nonneg _)
      (fun i => Paper.norm_parisiSlabExtend_sub_le (by norm_num) _ _ _) hnorm
  simpa only [mixedMagnetization, mixedGradient, mixedState, β, ν, νn,
    AdmissibleEvenMixture.unitClock, Function.comp_def, sub_add_cancel, zero_add] using he.add hfixed

theorem tendsto_mixedMagnetizationLaw_of_weak_and_time {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μn : ι → ParisiMeasure) (μ : ParisiMeasure) (hμ : Tendsto μn L (𝓝 μ))
    (qn : ι → Overlap) (q : Overlap) (hq : Tendsto qn L (𝓝 q)) :
    Tendsto (fun i => mixedMagnetizationLaw ξ h (μn i) (qn i)) L
      (𝓝 (mixedMagnetizationLaw ξ h μ q)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro g
  have he (ρ : ParisiMeasure) (r : Overlap) :
      (∫ x, g x ∂(mixedMagnetizationLaw ξ h ρ r : Measure ℝ)) =
        ∫ ω, g (mixedMagnetization ξ h ρ r ω) ∂Paper.canonicalBrownianMeasure := by
    change (∫ x, g x ∂Paper.canonicalBrownianMeasure.map (mixedMagnetization ξ h ρ r)) = _
    exact integral_map_of_stronglyMeasurable (measurable_mixedMagnetization ξ h ρ r)
      g.continuous.measurable.stronglyMeasurable
  simp_rw [he]
  apply tendsto_integral_filter_of_dominated_convergence (bound := fun _ => ‖g‖)
  · exact .of_forall fun i =>
      (g.continuous.measurable.comp (measurable_mixedMagnetization ξ h (μn i) (qn i))).aestronglyMeasurable
  · exact .of_forall fun _ => .of_forall fun _ => g.norm_coe_le_norm _
  · exact integrable_const _
  · exact .of_forall fun ω => g.continuous.continuousAt.tendsto.comp
      (tendsto_mixedMagnetization_of_weak_and_time ξ h μn μ hμ qn q hq ω)

end FourPapersCommon
