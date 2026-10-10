module
public import FourPapersCommon.MixedForkLaw
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.Topology.UniformSpace.HeineCantor

@[expose] public section

/-! Borel probability kernels and literal magnetization moments of the actual
Brownian fork. Moment continuity is proved by bounded convergence. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
namespace FourPapersCommon
set_option maxHeartbeats 1000000

theorem continuous_mixedForkMagnetization_times (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : Paper.ParisiMeasure) (sample : BrownianPair) :
    Continuous (fun p : Paper.Overlap×Paper.Overlap => mixedForkMagnetization ξ h μ p.1 p.2 sample) := by
  rw [continuous_iff_continuousAt]
  intro p
  exact tendsto_mixedForkMagnetization_of_weak_and_times ξ h (fun _ => μ) μ
    tendsto_const_nhds Prod.fst Prod.snd p.1 p.2
      continuous_fst.continuousAt.tendsto continuous_snd.continuousAt.tendsto sample

theorem continuous_mixedForkLaw (ξ : AdmissibleEvenMixture) (h : ℝ) :
    Continuous (fun p : Paper.ParisiMeasure×(Paper.Overlap×Paper.Overlap) =>
      mixedForkLaw ξ h p.1 p.2.1 p.2.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  exact tendsto_mixedForkLaw_of_weak_and_times ξ h Prod.fst p.1
    continuous_fst.continuousAt.tendsto (fun p => p.2.1) (fun p => p.2.2) p.2.1 p.2.2
      (continuous_fst.comp continuous_snd).continuousAt.tendsto
      (continuous_snd.comp continuous_snd).continuousAt.tendsto

theorem measurable_mixedForkLaw_measure_times (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : Paper.ParisiMeasure) :
    Measurable (fun p : Paper.Overlap×Paper.Overlap =>
      (mixedForkLaw ξ h μ p.1 p.2 : Measure (ℝ×ℝ))) := by
  let f : (Paper.Overlap×Paper.Overlap)×BrownianPair → ℝ×ℝ :=
    fun p => mixedForkMagnetization ξ h μ p.1.1 p.1.2 p.2
  have hf : Measurable f := measurable_uncurry_of_continuous_of_measurable
    (continuous_mixedForkMagnetization_times ξ h μ)
    (fun p => measurable_mixedForkMagnetization ξ h μ p.1 p.2)
  have hm : Measurable (fun p : Paper.Overlap×Paper.Overlap =>
      (brownianPairMeasure.map (Prod.mk p)).map f) :=
    (Measure.measurable_map f hf).comp Measurable.map_prodMk_left
  convert hm using 1
  funext p
  change brownianPairMeasure.map (mixedForkMagnetization ξ h μ p.1 p.2) = _
  rw [Measure.map_map hf measurable_prodMk_left]
  rfl

def mixedForkKernel (ξ : AdmissibleEvenMixture) (h : ℝ) (μ : Paper.ParisiMeasure) :
    Kernel (Paper.Overlap×Paper.Overlap) (ℝ×ℝ) where
  toFun p := (mixedForkLaw ξ h μ p.1 p.2 : Measure (ℝ×ℝ))
  measurable' := measurable_mixedForkLaw_measure_times ξ h μ

instance mixedForkKernel_isMarkov (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : Paper.ParisiMeasure) : IsMarkovKernel (mixedForkKernel ξ h μ) where
  isProbabilityMeasure p := inferInstanceAs (IsProbabilityMeasure
    (mixedForkLaw ξ h μ p.1 p.2 : Measure (ℝ×ℝ)))

def mixedForkMoment (ξ : AdmissibleEvenMixture) (h : ℝ) (μ : Paper.ParisiMeasure)
    (a b : ℕ) (r q : Paper.Overlap) : ℝ :=
  ∫ x : ℝ×ℝ, x.1^a*x.2^b ∂(mixedForkLaw ξ h μ r q : Measure (ℝ×ℝ))

theorem mixedForkMoment_eq_sample_integral (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : Paper.ParisiMeasure) (a b : ℕ) (r q : Paper.Overlap) :
    mixedForkMoment ξ h μ a b r q = ∫ sample,
      (mixedForkMagnetization ξ h μ r q sample).1^a*
        (mixedForkMagnetization ξ h μ r q sample).2^b ∂brownianPairMeasure := by
  change (∫ x : ℝ×ℝ, x.1^a*x.2^b
    ∂brownianPairMeasure.map (mixedForkMagnetization ξ h μ r q)) = _
  exact integral_map (measurable_mixedForkMagnetization ξ h μ r q).aemeasurable
    (continuous_fst.pow a |>.mul (continuous_snd.pow b)).measurable.aestronglyMeasurable

theorem mixedForkMagnetization_norm_bounds (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : Paper.ParisiMeasure) (r q : Paper.Overlap) (sample : BrownianPair) :
    ‖(mixedForkMagnetization ξ h μ r q sample).1‖ ≤ 1 ∧
      ‖(mixedForkMagnetization ξ h μ r q sample).2‖ ≤ 1 := by
  exact ⟨Paper.norm_parisiGradient_le_one _ _ _, Paper.norm_parisiGradient_le_one _ _ _⟩

theorem continuous_mixedForkMoment (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : Paper.ParisiMeasure) (a b : ℕ) :
    Continuous (fun p : Paper.Overlap×Paper.Overlap => mixedForkMoment ξ h μ a b p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  simp_rw [mixedForkMoment_eq_sample_integral]
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
  · exact Filter.Eventually.of_forall fun t =>
      (((measurable_mixedForkMagnetization ξ h μ t.1 t.2).fst.pow_const a).mul
        ((measurable_mixedForkMagnetization ξ h μ t.1 t.2).snd.pow_const b)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => Filter.Eventually.of_forall fun sample => by
      rw [norm_mul, norm_pow, norm_pow]
      have hbnd := mixedForkMagnetization_norm_bounds ξ h μ t.1 t.2 sample
      exact (mul_le_mul (pow_le_one₀ (norm_nonneg _) hbnd.1)
        (pow_le_one₀ (norm_nonneg _) hbnd.2) (by positivity) (by norm_num)).trans_eq (by norm_num)
  · exact integrable_const _
  · exact Filter.Eventually.of_forall fun sample =>
      (((continuous_mixedForkMagnetization_times ξ h μ sample).fst.pow a).mul
        ((continuous_mixedForkMagnetization_times ξ h μ sample).snd.pow b)).continuousAt.tendsto

theorem uniformContinuous_mixedForkMoment (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : Paper.ParisiMeasure) (a b : ℕ) :
    UniformContinuous (fun p : Paper.Overlap×Paper.Overlap => mixedForkMoment ξ h μ a b p.1 p.2) :=
  CompactSpace.uniformContinuous_of_continuous (continuous_mixedForkMoment ξ h μ a b)

end FourPapersCommon
