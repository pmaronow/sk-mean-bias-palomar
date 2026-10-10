module
public import QuantitativeFollowup.AnisotropicRecordedProfileMarkov
public import QuantitativeFollowup.AnisotropicSpinPathConditionals
public import QuantitativePaper.BrownianIndependentConditionalMean

@[expose] public section

/-! Conditional averaging of the genuine arbitrary-profile continuation.
The whole native past is retained, including the tilted initial disorder. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem anisotropicObservationParameter_native (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (p : AnisotropicDisorderBrownianSample n) :
    anisotropicObservationParameter D (anisotropicNativeObservation D μ q p)=
      anisotropicProcessParameter D μ q p := by
  simp only [anisotropicObservationParameter,anisotropicNativeObservation,
    anisotropicProcessParameter,anisotropicUnitInput,ContinuousLinearMap.comp_apply,
    anisotropicNoiseMap_inverseNoise]

theorem anisotropic_native_transition_conditional_mean (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q r : Paper.Overlap) (hqr : q≤r)
    (F : AnisotropicObservationState n→ℝ) (hF : Measurable F)
    (C : ℝ) (hC : ∀z,‖F z‖≤C) :
    (anisotropicMeasureSampleLaw D μ a)[(fun p=>F (anisotropicNativeObservation D μ r p))|
      anisotropicBrownianFiltration n (q:ℝ).toNNReal]=ᵐ[anisotropicMeasureSampleLaw D μ a]
      fun p=>∫z,F z∂anisotropicObservationTransition D μ q r (anisotropicNativeObservation D μ q p) := by
  let f : AnisotropicObservationState n×VectorWienerPath n→ℝ :=
    F ∘ anisotropicObservationNoiseAdvance D μ q r
  have hf : Measurable f:=hF.comp (measurable_anisotropicObservationNoiseAdvance D μ q r)
  have hh:=condExp_independent_noise (anisotropicBrownianFiltration n (q:ℝ).toNNReal)
    (anisotropicMeasureSampleLaw D μ a) ((anisotropicBrownianFiltration n).le _)
    (anisotropicNativeObservation D μ q) (adapted_anisotropicNativeObservation D μ q)
    (anisotropicRecordedFutureBrownianPath (q:ℝ).toNNReal) (measurable_anisotropicRecordedFutureBrownianPath _)
    (vectorWienerMeasure n) (hasLaw_anisotropicRecordedFutureBrownianPath D μ a _)
    (indep_anisotropicRecordedFutureBrownianPath_filtration D μ a _) f hf C (fun z=>hC _)
  have he : (fun p=>f (anisotropicNativeObservation D μ q p,
      anisotropicRecordedFutureBrownianPath (q:ℝ).toNNReal p))=
      fun p=>F (anisotropicNativeObservation D μ r p) := by
    funext p
    exact congrArg F (anisotropicNativeObservation_advance D μ q r hqr p)
  rw [he] at hh
  exact hh.trans (.of_forall fun p=>by
    change (∫z,f (anisotropicNativeObservation D μ q p,z)∂vectorWienerMeasure n)=
      ∫z,F z∂anisotropicObservationTransition D μ q r (anisotropicNativeObservation D μ q p)
    rw [anisotropicObservationTransition_apply]
    exact (integral_map
      (μ:=vectorWienerMeasure n) (φ:=fun W=>anisotropicObservationNoiseAdvance D μ q r
        (anisotropicNativeObservation D μ q p,W)) (f:=F)
      ((measurable_anisotropicObservationNoiseAdvance D μ q r).comp
        (measurable_const.prodMk measurable_id)).aemeasurable hF.aestronglyMeasurable).symm)

/-- The normalized terminal-spin continuation from an arbitrary current state. -/
def anisotropicObservationTerminalSpinKernel (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    Kernel (AnisotropicObservationState n) (Configuration n) :=
  ((anisotropicTerminalSpinKernel D).comap (anisotropicObservationParameter D)
    (measurable_anisotropicObservationParameter D)) ∘ₖ anisotropicObservationTransition D μ q 1

instance anisotropicObservationTerminalSpinKernel_markov (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    IsMarkovKernel (anisotropicObservationTerminalSpinKernel D μ q) := by
  unfold anisotropicObservationTerminalSpinKernel
  infer_instance

theorem anisotropicObservationTerminalSpinKernel_mean (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (d : Configuration n→ℝ)
    (z : AnisotropicObservationState n) :
    (∫σ,d σ∂anisotropicObservationTerminalSpinKernel D μ q z)=
      ∫y,anisotropicTerminalFeatureMean D d (anisotropicObservationParameter D y)
        ∂anisotropicObservationTransition D μ q 1 z := by
  let C:=∑σ : Configuration n,‖d σ‖
  have hi : Integrable d (anisotropicObservationTerminalSpinKernel D μ q z) :=
    (integrable_const C).mono' (measurable_of_finite d).aestronglyMeasurable
      (.of_forall fun σ=>Finset.single_le_sum (fun τ _=>norm_nonneg (d τ)) (Finset.mem_univ σ))
  exact Kernel.integral_comp hi

theorem anisotropic_terminal_continuation_conditional_mean (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (d : Configuration n→ℝ) :
    (anisotropicMeasureSampleLaw D μ a)[anisotropicTerminalObservable D μ d|
      anisotropicBrownianFiltration n (q:ℝ).toNNReal]=ᵐ[anisotropicMeasureSampleLaw D μ a]
      fun p=>∫σ,d σ∂anisotropicObservationTerminalSpinKernel D μ q (anisotropicNativeObservation D μ q p) := by
  let C:=∑σ : Configuration n,‖d σ‖
  have hd (σ : Configuration n) : ‖d σ‖≤C:=
    Finset.single_le_sum (fun τ _=>norm_nonneg (d τ)) (Finset.mem_univ σ)
  have hh:=anisotropic_native_transition_conditional_mean D μ a q 1 q.property.2
    (fun z=>anisotropicTerminalFeatureMean D d (anisotropicObservationParameter D z))
    ((measurable_anisotropicTerminalFeatureMean D d).comp (measurable_anisotropicObservationParameter D))
    C (fun z=>anisotropicTerminalFeatureMean_bound D d C hd _)
  have he : (fun p=>anisotropicTerminalFeatureMean D d
      (anisotropicObservationParameter D (anisotropicNativeObservation D μ 1 p)))=
      anisotropicTerminalObservable D μ d := by
    funext p
    rw [anisotropicObservationParameter_native]
    rfl
  rw [he] at hh
  exact hh.trans (.of_forall fun p=>(anisotropicObservationTerminalSpinKernel_mean D μ q d _).symm)

end QuantitativeFollowup
