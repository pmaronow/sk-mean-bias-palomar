module
public import HexagonPaper.EdgeLikelihoodStoppedFinitePath
public import FRSB.MeasureApproximation
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

@[expose] public section

/-! Arbitrary-profile stopped edge path likelihood from actual finite-profile path
laws, common-noise path convergence, and one Gaussian exponential envelope. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace HexagonPaper
open FourPapersCommon QuantitativePaper QuantitativeFollowup
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def edgeStoppedGaussianLaw (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (q h : Paper.Overlap) (x : Field n) :
    Measure C(Paper.Overlap,AnisotropicParameter n) :=
  ((vectorDisorderBrownianMeasure n).withDensity
    (fun sample=>edgeStoppedLikelihood D μ q h (edgeStoppedReferencePath D g q h x sample))).map
      (edgeStoppedReferencePath D g q h x)

theorem measurable_edgeStoppedLikelihood (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (q h : Paper.Overlap) (x : Field n) :
    Measurable (fun sample : VectorDisorderBrownianSample n=>
      edgeStoppedLikelihood D μ q h (edgeStoppedReferencePath D g q h x sample)) := by
  have hm:=ENNReal.measurable_ofReal.comp (measurable_edgeStoppedLikelihood_toReal D μ g q h x)
  simpa only [edgeStoppedLikelihood,ENNReal.toReal_ofReal (Real.exp_pos _).le,
    Function.comp_def] using hm

instance edgeStoppedGaussianLaw_finite (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (q h : Paper.Overlap) (x : Field n) :
    IsFiniteMeasure (edgeStoppedGaussianLaw D μ g q h x) := by
  have hi:=integrable_edgeStoppedLikelihood_toReal D μ g q h x
  have he:=ofReal_integral_eq_lintegral_ofReal hi
    (.of_forall fun _=>ENNReal.toReal_nonneg)
  have hf (sample : VectorDisorderBrownianSample n) :
      edgeStoppedLikelihood D μ q h (edgeStoppedReferencePath D g q h x sample)≠∞ := ENNReal.ofReal_ne_top
  simp_rw [ENNReal.ofReal_toReal (hf _)] at he
  haveI := isFiniteMeasure_withDensity (μ:=vectorDisorderBrownianMeasure n)
    (f:=fun sample=>edgeStoppedLikelihood D μ q h (edgeStoppedReferencePath D g q h x sample))
    (by rw [←he];exact ENNReal.ofReal_ne_top)
  unfold edgeStoppedGaussianLaw
  infer_instance

theorem integral_edgeStoppedGaussianLaw_boundedContinuous
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n)
    (q h : Paper.Overlap) (x : Field n)
    (f : BoundedContinuousFunction C(Paper.Overlap,AnisotropicParameter n) ℝ) :
    (∫Z,f Z ∂edgeStoppedGaussianLaw D μ g q h x)=
      ∫sample,(edgeStoppedLikelihood D μ q h (edgeStoppedReferencePath D g q h x sample)).toReal*
        f (edgeStoppedReferencePath D g q h x sample) ∂vectorDisorderBrownianMeasure n := by
  unfold edgeStoppedGaussianLaw
  rw [integral_map (measurable_edgeStoppedReferencePath D g q h x).aemeasurable
    f.continuous.measurable.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_edgeStoppedLikelihood D μ g q h x)
      (.of_forall fun _=>lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)]
  rfl

theorem edge_stopped_continuous_path_likelihood
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (q h : Paper.Overlap) (hqh : q≤h) (x : Field n) :
    (vectorDisorderBrownianMeasure n).map (edgeStoppedDiffusionPath D μ g q h x)=
      edgeStoppedGaussianLaw D μ g q h x := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let μj:=FRSB.preservingMeasure μ ∅
  have hj:=FRSB.tendsto_preservingMeasure μ ∅
  have hphysical : Tendsto (fun j=>∫sample,f (edgeStoppedDiffusionPath D (μj j) g q h x sample)
      ∂vectorDisorderBrownianMeasure n) atTop
      (𝓝 (∫sample,f (edgeStoppedDiffusionPath D μ g q h x sample) ∂vectorDisorderBrownianMeasure n)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _=>‖f‖)
    · exact .of_forall fun j=> (f.continuous.measurable.comp
        (measurable_edgeStoppedDiffusionPath D (μj j) g q h x)).aestronglyMeasurable
    · exact .of_forall fun _=>.of_forall fun _=>f.norm_coe_le_norm _
    · exact integrable_const _
    · exact .of_forall fun sample=>f.continuous.continuousAt.tendsto.comp
        (tendsto_edgeStoppedDiffusionPath_profile D hj g q h x sample)
  have hreference : Tendsto (fun j=>∫sample,
      (edgeStoppedLikelihood D (μj j) q h (edgeStoppedReferencePath D g q h x sample)).toReal*
        f (edgeStoppedReferencePath D g q h x sample) ∂vectorDisorderBrownianMeasure n) atTop
      (𝓝 (∫sample,(edgeStoppedLikelihood D μ q h (edgeStoppedReferencePath D g q h x sample)).toReal*
        f (edgeStoppedReferencePath D g q h x sample) ∂vectorDisorderBrownianMeasure n)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun sample=>‖f‖*edgeSuffixGaussianEnvelope D μ g x sample)
    · exact .of_forall fun j=>((measurable_edgeStoppedLikelihood_toReal D (μj j) g q h x).mul
        (f.continuous.measurable.comp (measurable_edgeStoppedReferencePath D g q h x))).aestronglyMeasurable
    · exact .of_forall fun j=>.of_forall fun sample=>by
        rw [norm_mul]
        exact (mul_le_mul (edgeStoppedLikelihood_gaussian_envelope D (μj j) μ g q h x sample)
          (f.norm_coe_le_norm _) (norm_nonneg _) (by unfold edgeSuffixGaussianEnvelope;positivity)).trans_eq
            (mul_comm _ _)
    · exact (integrable_edgeSuffixGaussianEnvelope D μ g x).const_mul ‖f‖
    · exact .of_forall fun sample=>
        (tendsto_edgeStoppedLikelihood_toReal_profile D hj q h (edgeStoppedReferencePath D g q h x sample)).mul_const _
  have he (j : ℕ) : (∫sample,f (edgeStoppedDiffusionPath D (μj j) g q h x sample)
      ∂vectorDisorderBrownianMeasure n)=
      ∫sample,(edgeStoppedLikelihood D (μj j) q h (edgeStoppedReferencePath D g q h x sample)).toReal*
        f (edgeStoppedReferencePath D g q h x sample) ∂vectorDisorderBrownianMeasure n := by
    have hl:=edge_stopped_continuous_path_likelihood_finite D (μj j)
      (FRSB.finite_support_preservingMeasure μ ∅ j) g q h hqh x
    change (vectorDisorderBrownianMeasure n).map (edgeStoppedDiffusionPath D (μj j) g q h x)=
      edgeStoppedGaussianLaw D (μj j) g q h x at hl
    have hi:=congrArg (fun P : Measure C(Paper.Overlap,AnisotropicParameter n)=>∫Z,f Z ∂P) hl
    rw [integral_map (measurable_edgeStoppedDiffusionPath D (μj j) g q h x).aemeasurable
      f.continuous.measurable.aestronglyMeasurable,
      integral_edgeStoppedGaussianLaw_boundedContinuous] at hi
    exact hi
  have hlim:=tendsto_nhds_unique hphysical (by simpa only [he] using hreference)
  rw [integral_map (measurable_edgeStoppedDiffusionPath D μ g q h x).aemeasurable
    f.continuous.measurable.aestronglyMeasurable,integral_edgeStoppedGaussianLaw_boundedContinuous]
  exact hlim

end HexagonPaper
