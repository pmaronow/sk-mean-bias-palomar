module
public import QuantitativePaper.VectorMeasureGradientAdaptation
public import FourPapersCommon.ConditionalKernelExpectation

@[expose] public section

/-! A literal conditional expectation for the actual arbitrary-profile
terminal Gibbs mean, under every real fractional disorder tilt. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

theorem vectorMeasure_terminal_mean_condExp (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) (l : Fin n) :
    (vectorMeasureDisorderTilt μ β t a)[
      (fun sample=>terminalMean
        (vectorTerminalExponent n β t sample.1 (vectorMeasureState μ β t ht.le 1 sample))
        (fun σ=>Paper.spinSign (σ l))) |
      vectorBrownianFiltration n (q : ℝ).toNNReal]=ᵐ[vectorMeasureDisorderTilt μ β t a]
      fun sample=>vectorMeasureSpinMean μ β t ht.le q sample l := by
  haveI := vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht.le
  have hd : ∀σ : Configuration n,|Paper.spinSign (σ l)|≤(1 : ℝ) :=
    fun σ=>le_of_eq (Paper.abs_spinSign (σ l))
  have hmean : Measurable (fun sample : VectorDisorderBrownianSample n=>terminalMean
      (vectorTerminalExponent n β t sample.1 (vectorMeasureState μ β t ht.le 1 sample))
      (fun σ=>Paper.spinSign (σ l))) := by
    have hm := (continuous_vectorTerminalMean_joint β t
      (fun σ=>Paper.spinSign (σ l))).measurable.comp
        (measurable_vectorMeasureJointState (n:=n) μ β t ht.le 1)
    dsimp only [Function.comp_def,vectorMeasureJointState] at hm
    exact hm
  have hi : Integrable (fun sample : VectorDisorderBrownianSample n=>terminalMean
      (vectorTerminalExponent n β t sample.1 (vectorMeasureState μ β t ht.le 1 sample))
      (fun σ=>Paper.spinSign (σ l))) (vectorMeasureDisorderTilt μ β t a) :=
    (integrable_const (1 : ℝ)).mono' hmean.aestronglyMeasurable
      (.of_forall fun _=>by simpa only [Real.norm_eq_abs] using terminalMean_bound _ _ 1 hd)
  have had := adapted_vectorMeasureSpinMean_component μ β t ht.le q l
  have hci : Integrable (fun sample=>vectorMeasureSpinMean μ β t ht.le q sample l)
      (vectorMeasureDisorderTilt μ β t a) :=
    (integrable_const (1 : ℝ)).mono'
      (had.mono ((vectorBrownianFiltration n).le _) le_rfl).aestronglyMeasurable
      (.of_forall fun sample=>by simpa only [Real.norm_eq_abs] using
        vectorMeasureSpinMean_component_bound μ β t ht.le q sample l)
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq ((vectorBrownianFiltration n).le _) hi
  · intro A hA hfinite
    exact hci.integrableOn
  · intro A hA hfinite
    have hAg : MeasurableSet A := ((vectorBrownianFiltration n).le _) A hA
    have he := vectorMeasure_terminal_spin_pairing_past μ β t a hβ ht q l
      (A.indicator (fun _=>1)) (measurable_const.indicator hA) 1
      (fun sample=>by
        by_cases hs : sample∈A
        · simp only [indicator_of_mem hs,norm_one,NNReal.coe_one,le_refl]
        · simp only [indicator_of_notMem hs,norm_zero,NNReal.coe_one,zero_le_one])
    rw [integral_indicator_one_mul_eq_setIntegral
        (vectorMeasureDisorderTilt μ β t a) A
        hAg,
      integral_indicator_one_mul_eq_setIntegral
        (vectorMeasureDisorderTilt μ β t a) A
        hAg] at he
    exact he.symm
  · exact had.stronglyMeasurable.aestronglyMeasurable

end QuantitativePaper
