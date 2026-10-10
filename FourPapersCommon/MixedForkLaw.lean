module
public import FourPapersCommon.BrownianForkPath
public import FourPapersCommon.ParisiNoiseContinuity
public import FourPapersCommon.MixedMagnetizationContinuity

@[expose] public section

/-! Actual two-magnetization fork law on a product Brownian space.  Each
marginal is the actual selected diffusion's magnetization law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
namespace FourPapersCommon
set_option maxHeartbeats 1000000

def mixedNoiseMagnetization (ξ : AdmissibleEvenMixture) (h : ℝ) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (W : C(Icc (0 : ℝ) 1,ℝ)) : ℝ :=
  mixedGradient ξ μ ((q : ℝ),
    parisiNoiseStatePath (mixedBeta ξ) h (mixedMeasure ξ μ) W (ξ.unitClock q))

theorem continuous_mixedNoiseMagnetization (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) : Continuous (mixedNoiseMagnetization ξ h μ q) := by
  change Continuous (fun W => Paper.parisiGradient (mixedBeta ξ) (mixedMeasure ξ μ)
    (ξ.clock (q : ℝ), parisiNoiseStatePath (mixedBeta ξ) h (mixedMeasure ξ μ) W (ξ.unitClock q)))
  exact ((Paper.continuous_parisiGradient _ _).comp
    (continuous_const.prodMk ((continuous_eval_const _).comp
      (continuous_parisiNoiseStatePath _ _ _))))

@[simp] theorem mixedNoiseMagnetization_canonical (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (sample : Paper.BrownianSample) :
    mixedNoiseMagnetization ξ h μ q (Paper.canonicalBrownianPath sample) =
      mixedMagnetization ξ h μ q sample := by
  exact congrArg (fun x => mixedGradient ξ μ ((q : ℝ),x))
    (parisiNoiseStatePath_canonical (mixedBeta ξ) h (mixedBeta_ne_zero ξ)
      (mixedMeasure ξ μ) sample (ξ.unitClock q))

theorem tendsto_mixedNoiseMagnetization_of_weak_noise_time {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μn : ι → Paper.ParisiMeasure) (μ : Paper.ParisiMeasure) (hμ : Tendsto μn L (𝓝 μ))
    (qn : ι → Paper.Overlap) (q : Paper.Overlap) (hq : Tendsto qn L (𝓝 q))
    (Wn : ι → C(Icc (0 : ℝ) 1,ℝ)) (W : C(Icc (0 : ℝ) 1,ℝ))
    (hW : Tendsto Wn L (𝓝 W)) :
    Tendsto (fun i => mixedNoiseMagnetization ξ h (μn i) (qn i) (Wn i)) L
      (𝓝 (mixedNoiseMagnetization ξ h μ q W)) := by
  let β := mixedBeta ξ
  let ν := mixedMeasure ξ μ
  let νn := fun i => mixedMeasure ξ (μn i)
  have hν : Tendsto νn L (𝓝 ν) := (continuous_mixedMeasure ξ).continuousAt.tendsto.comp hμ
  have ht := ξ.continuous_unitClock.continuousAt.tendsto.comp hq
  have hs := tendsto_parisiNoiseStatePath_of_weak_and_noise β h νn ν hν Wn W hW
  have heval := continuous_eval.continuousAt.tendsto.comp (hs.prodMk_nhds ht)
  have hg := (Paper.continuous_parisiGradient β ν).continuousAt.tendsto.comp
    ((continuous_subtype_val.continuousAt.tendsto.comp ht).prodMk_nhds heval)
  have hnorm : Tendsto (fun i => ‖Paper.parisiGradientBCF β (νn i)-Paper.parisiGradientBCF β ν‖)
      L (𝓝 0) := by
    simpa using (((FRSB.continuous_gradientBCF β).continuousAt.tendsto.comp hν).sub_const
      (Paper.parisiGradientBCF β ν)).norm
  have herr : Tendsto (fun i =>
      Paper.parisiGradient β (νn i) ((ξ.unitClock (qn i) : ℝ),
        parisiNoiseStatePath β h (νn i) (Wn i) (ξ.unitClock (qn i))) -
      Paper.parisiGradient β ν ((ξ.unitClock (qn i) : ℝ),
        parisiNoiseStatePath β h (νn i) (Wn i) (ξ.unitClock (qn i)))) L (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun i =>
      Paper.norm_parisiSlabExtend_sub_le (by norm_num) _ _ _) hnorm
  simpa only [mixedNoiseMagnetization, mixedGradient, β, ν, νn,
    AdmissibleEvenMixture.unitClock, Function.comp_def, sub_add_cancel, zero_add] using herr.add hg

def mixedForkMagnetization (ξ : AdmissibleEvenMixture) (h : ℝ) (μ : Paper.ParisiMeasure)
    (r q : Paper.Overlap) (sample : BrownianPair) : ℝ×ℝ :=
  (mixedMagnetization ξ h μ q sample.1,
    mixedNoiseMagnetization ξ h μ q (forkBrownianPath (ξ.clock (r : ℝ)).toNNReal sample))

theorem measurable_mixedForkMagnetization (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : Paper.ParisiMeasure) (r q : Paper.Overlap) :
    Measurable (mixedForkMagnetization ξ h μ r q) :=
  ((measurable_mixedMagnetization ξ h μ q).comp measurable_fst).prodMk
    ((continuous_mixedNoiseMagnetization ξ h μ q).measurable.comp
      (measurable_forkBrownianPath _))

def mixedForkLaw (ξ : AdmissibleEvenMixture) (h : ℝ) (μ : Paper.ParisiMeasure)
    (r q : Paper.Overlap) : ProbabilityMeasure (ℝ×ℝ) :=
  ProbabilityMeasure.map (⟨brownianPairMeasure, inferInstance⟩ : ProbabilityMeasure BrownianPair)
    (mixedForkMagnetization ξ h μ r q)

theorem mixedForkLaw_fst (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : Paper.ParisiMeasure) (r q : Paper.Overlap) :
    (mixedForkLaw ξ h μ r q : Measure (ℝ×ℝ)).map Prod.fst =
      (mixedMagnetizationLaw ξ h μ q : Measure ℝ) := by
  change (brownianPairMeasure.map (mixedForkMagnetization ξ h μ r q)).map Prod.fst =
    Paper.canonicalBrownianMeasure.map (mixedMagnetization ξ h μ q)
  rw [Measure.map_map measurable_fst (measurable_mixedForkMagnetization ξ h μ r q)]
  change brownianPairMeasure.map (mixedMagnetization ξ h μ q ∘ Prod.fst) = _
  rw [← Measure.map_map (measurable_mixedMagnetization ξ h μ q) measurable_fst]
  have hp : MeasurePreserving (Prod.fst : BrownianPair → Paper.BrownianSample)
      brownianPairMeasure Paper.canonicalBrownianMeasure := measurePreserving_fst
  exact congrArg (fun P => P.map (mixedMagnetization ξ h μ q)) hp.map_eq

theorem mixedForkLaw_snd (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : Paper.ParisiMeasure) (r q : Paper.Overlap) :
    (mixedForkLaw ξ h μ r q : Measure (ℝ×ℝ)).map Prod.snd =
      (mixedMagnetizationLaw ξ h μ q : Measure ℝ) := by
  change (brownianPairMeasure.map (mixedForkMagnetization ξ h μ r q)).map Prod.snd =
    Paper.canonicalBrownianMeasure.map (mixedMagnetization ξ h μ q)
  rw [Measure.map_map measurable_snd (measurable_mixedForkMagnetization ξ h μ r q)]
  change brownianPairMeasure.map (mixedNoiseMagnetization ξ h μ q ∘
    forkBrownianPath (ξ.clock (r : ℝ)).toNNReal) = _
  rw [← Measure.map_map (continuous_mixedNoiseMagnetization ξ h μ q).measurable
    (measurable_forkBrownianPath _), forkBrownianPath_law]
  change (Paper.canonicalBrownianMeasure.map Paper.canonicalBrownianPath).map
    (mixedNoiseMagnetization ξ h μ q) = _
  rw [Measure.map_map (continuous_mixedNoiseMagnetization ξ h μ q).measurable
    Paper.measurable_canonicalBrownianPath]
  congr 1
  funext sample
  exact mixedNoiseMagnetization_canonical ξ h μ q sample

theorem tendsto_mixedForkMagnetization_of_weak_and_times {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μn : ι → Paper.ParisiMeasure) (μ : Paper.ParisiMeasure) (hμ : Tendsto μn L (𝓝 μ))
    (rn qn : ι → Paper.Overlap) (r q : Paper.Overlap)
    (hr : Tendsto rn L (𝓝 r)) (hq : Tendsto qn L (𝓝 q)) (sample : BrownianPair) :
    Tendsto (fun i => mixedForkMagnetization ξ h (μn i) (rn i) (qn i) sample) L
      (𝓝 (mixedForkMagnetization ξ h μ r q sample)) := by
  have hrc : Tendsto (fun i => (ξ.clock (rn i)).toNNReal) L (𝓝 (ξ.clock r).toNNReal) :=
    continuous_real_toNNReal.continuousAt.tendsto.comp
      (continuous_subtype_val.continuousAt.tendsto.comp
        (ξ.continuous_unitClock.continuousAt.tendsto.comp hr))
  have hW := (continuous_forkBrownianPath_split sample).continuousAt.tendsto.comp hrc
  exact (tendsto_mixedMagnetization_of_weak_and_time ξ h μn μ hμ qn q hq sample.1).prodMk_nhds
    (tendsto_mixedNoiseMagnetization_of_weak_noise_time ξ h μn μ hμ qn q hq _ _ hW)

theorem tendsto_mixedForkLaw_of_weak_and_times {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μn : ι → Paper.ParisiMeasure) (μ : Paper.ParisiMeasure) (hμ : Tendsto μn L (𝓝 μ))
    (rn qn : ι → Paper.Overlap) (r q : Paper.Overlap)
    (hr : Tendsto rn L (𝓝 r)) (hq : Tendsto qn L (𝓝 q)) :
    Tendsto (fun i => mixedForkLaw ξ h (μn i) (rn i) (qn i)) L (𝓝 (mixedForkLaw ξ h μ r q)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro g
  have he (ν : Paper.ParisiMeasure) (a b : Paper.Overlap) :
      (∫ x, g x ∂(mixedForkLaw ξ h ν a b : Measure (ℝ×ℝ))) =
        ∫ sample, g (mixedForkMagnetization ξ h ν a b sample) ∂brownianPairMeasure := by
    change (∫ x, g x ∂brownianPairMeasure.map (mixedForkMagnetization ξ h ν a b)) = _
    exact integral_map (measurable_mixedForkMagnetization ξ h ν a b).aemeasurable
      g.continuous.measurable.aestronglyMeasurable
  simp_rw [he]
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => ‖g‖)
  · exact Filter.Eventually.of_forall fun i =>
      (g.continuous.measurable.comp (measurable_mixedForkMagnetization ξ h (μn i) (rn i) (qn i))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun _ => Filter.Eventually.of_forall fun _ => g.norm_coe_le_norm _
  · exact integrable_const _
  · exact Filter.Eventually.of_forall fun sample => g.continuous.continuousAt.tendsto.comp
      (tendsto_mixedForkMagnetization_of_weak_and_times ξ h μn μ hμ rn qn r q hr hq sample)

end FourPapersCommon
