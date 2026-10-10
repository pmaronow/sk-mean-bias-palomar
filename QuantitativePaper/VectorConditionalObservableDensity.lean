module
public import FourPapersCommon.PastDensityConditionalExpectation
public import QuantitativePaper.VectorMeasureMarkedConditionalLaw

@[expose] public section

/-! The actual fractional disorder tilt is known in the whole past at every
time. Conditional terminal observables can therefore be evaluated under the
fixed product Wiener law; this is proved by density transport. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace QuantitativePaper
open FourPapersCommon
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

theorem vectorMeasureTerminalObservable_condExp_eq_base (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) (d : Configuration n→ℝ) :
    (vectorMeasureDisorderTilt μ β t a)[vectorMeasureTerminalObservable μ β t ht d|
      vectorBrownianFiltration n (q:ℝ).toNNReal]
      =ᵐ[vectorMeasureDisorderTilt μ β t a]
        (vectorDisorderBrownianMeasure n)[vectorMeasureTerminalObservable μ β t ht d|
          vectorBrownianFiltration n (q:ℝ).toNNReal] := by
  let P:=vectorDisorderBrownianMeasure n
  let w:=fun sample : VectorDisorderBrownianSample n=>vectorMeasureOuterWeight μ β t a sample.1
  let F:=vectorMeasureTerminalObservable μ β t ht d
  have hw : StronglyMeasurable[vectorBrownianFiltration n (q:ℝ).toNNReal] w :=
    (measurable_vectorMeasureOuterWeight μ β t a ht).stronglyMeasurable.comp_measurable
      (stronglyMeasurable_initialVectorDisorder n (q:ℝ).toNNReal).measurable
  have hwm : Measurable w :=
    (measurable_vectorMeasureOuterWeight μ β t a ht).comp measurable_fst
  have hwn (sample : VectorDisorderBrownianSample n) : 0≤w sample := by
    exact div_nonneg (Real.exp_pos _).le (vectorMeasureOuterPartition_pos μ β t a ht).le
  haveI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  haveI : IsFiniteMeasure (P.withDensity (fun sample=>ENNReal.ofReal (w sample))) :=
    inferInstanceAs (IsFiniteMeasure (vectorMeasureDisorderTilt (n:=n) μ β t a))
  let D:=∑σ : Configuration n,|d σ|
  have hF : Integrable F P := by
    apply (integrable_const D).mono'
      (measurable_vectorMeasureTerminalObservable μ β t ht d).aestronglyMeasurable
    exact .of_forall fun sample=>by
      rw [Real.norm_eq_abs]
      exact terminalMean_bound _ d D (fun σ=>
        Finset.single_le_sum (fun τ _=>abs_nonneg (d τ)) (Finset.mem_univ σ))
  have hwF : Integrable (w*F) P := by
    change Integrable (fun x=>w x*F x) P
    have hQ:=integrable_vectorMeasureTerminalObservable μ β t a ht d
    have he:=(integrable_withDensity_iff_integrable_smul' hwm.ennreal_ofReal
      (.of_forall fun _=>ENNReal.ofReal_lt_top)).mp hQ
    simpa only [ENNReal.toReal_ofReal (hwn _),smul_eq_mul, P, F, Pi.mul_apply] using he
  exact condExp_withDensity_of_pastWeight (vectorBrownianFiltration n (q:ℝ).toNNReal)
    ((vectorBrownianFiltration n).le _) w F hw hwn hF hwF

end QuantitativePaper
