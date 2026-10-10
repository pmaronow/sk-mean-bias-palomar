module
public import QuantitativeFollowup.VectorMeanOverlap
public import QuantitativePaper.VectorMeasureTerminalGradient
public import QuantitativePaper.VectorFeedbackControl

@[expose] public section

/-! Actual terminal-gradient/control pairing and its quadratic expectation,
under the genuine fractional tilt and every physical time. -/
noncomputable section
open Set MeasureTheory QuantitativePaper FourPapersCommon
open scoped NNReal BigOperators Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vectorTerminalGradient_component (β t : ℝ) (p : Couplings n×ℝ)
    (x : Field n) (l : Fin n) :
    vectorTerminalGradient n β t p x l=terminalMean (vectorTerminalExponent n β t p x)
      (fun σ=>Paper.spinSign (σ l)) := by
  rw [vectorTerminalGradient_eq_magnetization]
  simp only [vectorMagnetization,vectorObservableResponse,vectorTerminalObservable,terminalTilt_zero]

theorem vectorMeasureFeedbackControl_eq_spinMean (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (r : ℝ≥0) (hr : r≤1) (sample : VectorDisorderBrownianSample n) :
    vectorMeasureFeedbackControl (n:=n) μ β t ht r sample=
      vectorMeasureSpinMean μ β t ht ⟨r,⟨r.coe_nonneg,hr⟩⟩ sample := by
  simp only [vectorMeasureFeedbackControl,vectorMeasureSpinMean,projIcc_of_mem zero_le_one
    (show (r:ℝ)∈Icc (0:ℝ) 1 from ⟨r.coe_nonneg,hr⟩),Real.toNNReal_coe]

theorem vector_feedback_terminal_component_pairing (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (r : ℝ≥0) (hr : r≤1) (l : Fin n) :
    (∫sample,vectorTerminalGradient n β t sample.1
        (vectorControlledState ((1-t)*β^2) μ (vectorMeasureFeedbackControl (n:=n) μ β t ht.le) 1 sample) l*
      vectorMeasureFeedbackControl (n:=n) μ β t ht.le r sample l ∂vectorMeasureDisorderTilt μ β t a)=
    ∫sample,(vectorMeasureFeedbackControl (n:=n) μ β t ht.le r sample l)^2
      ∂vectorMeasureDisorderTilt μ β t a := by
  let q : Paper.Overlap:=⟨r,⟨r.coe_nonneg,hr⟩⟩
  have hZ:=adapted_vectorMeasureSpinMean_component μ β t ht.le q l
  have hb (sample : VectorDisorderBrownianSample n) :
      ‖vectorMeasureSpinMean μ β t ht.le q sample l‖≤(1:ℝ≥0):=by
    simpa only [Real.norm_eq_abs,NNReal.coe_one] using
      vectorMeasureSpinMean_component_bound μ β t ht.le q sample l
  have hh:=vectorMeasure_terminal_spin_pairing_past μ β t a hβ ht q l _ hZ 1 hb
  simp_rw [vectorTerminalGradient_component,
    ←vectorMeasureState_eq_controlled μ β t ht.le 1 le_rfl,
    vectorMeasureFeedbackControl_eq_spinMean μ β t ht.le r hr]
  simpa only [q,pow_two,mul_comm] using hh

theorem integrable_vector_feedback_terminal_component (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (r : ℝ≥0) (hr : r≤1) (l : Fin n) :
    Integrable (fun sample=>vectorTerminalGradient n β t sample.1
        (vectorControlledState ((1-t)*β^2) μ (vectorMeasureFeedbackControl (n:=n) μ β t ht) 1 sample) l*
      vectorMeasureFeedbackControl (n:=n) μ β t ht r sample l) (vectorMeasureDisorderTilt μ β t a) := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  let A:=vectorMeasureFeedbackControl (n:=n) μ β t ht
  have hA:=isVectorParisiControl_vectorMeasureFeedbackControl (n:=n) μ β t ht
  have hv:=((EuclideanSpace.proj l).continuous.measurable.comp
    ((continuous_vectorTerminalGradient (n:=n) β t).measurable.comp
      (measurable_fst.prodMk ((measurable_vectorControlledState ((1-t)*β^2) μ A hA).of_uncurry_left (x:=1)))))
  have ha:=((EuclideanSpace.proj l).continuous.measurable.comp (hA.measurable.of_uncurry_left (x:=r)))
  apply (integrable_const (1:ℝ)).mono' (hv.mul ha).aestronglyMeasurable
  filter_upwards with sample
  change ‖vectorTerminalGradient n β t sample.1 (vectorControlledState ((1-t)*β^2) μ A 1 sample) l*A r sample l‖≤1
  rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,vectorTerminalGradient_component]
  have hd (σ : Configuration n) : |Paper.spinSign (σ l)|≤(1:ℝ):=(Paper.abs_spinSign _).le
  have hb:=terminalMean_bound (vectorTerminalExponent n β t sample.1
    (vectorControlledState ((1-t)*β^2) μ A 1 sample)) _ 1 hd
  have hc : |A r sample l|≤1:=by
    change |vectorMeasureFeedbackControl (n:=n) μ β t ht r sample l|≤1
    rw [vectorMeasureFeedbackControl_eq_spinMean μ β t ht r hr]
    exact vectorMeasureSpinMean_component_bound μ β t ht _ sample l
  exact (mul_le_mul hb hc (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem vector_feedback_terminal_pairing (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (r : ℝ≥0) (hr : r≤1) :
    (∫sample,inner ℝ (vectorTerminalGradient n β t sample.1
        (vectorControlledState ((1-t)*β^2) μ (vectorMeasureFeedbackControl (n:=n) μ β t ht.le) 1 sample))
      (vectorMeasureFeedbackControl (n:=n) μ β t ht.le r sample) ∂vectorMeasureDisorderTilt μ β t a)=
      ∫sample,‖vectorMeasureFeedbackControl (n:=n) μ β t ht.le r sample‖^2
        ∂vectorMeasureDisorderTilt μ β t a := by
  simp_rw [PiLp.inner_apply,Real.inner_apply,EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum _ (fun l _=>integrable_vector_feedback_terminal_component μ β t a ht.le r hr l),
    integral_finsetSum _ (fun l _=>by
      simp_rw [vectorMeasureFeedbackControl_eq_spinMean μ β t ht.le r hr,pow_two]
      exact integrable_vectorMeanOverlap_mul μ β t a ht.le _ _ l)]
  exact Finset.sum_congr rfl (fun l _=>vector_feedback_terminal_component_pairing μ β t a hβ ht r hr l)

theorem vector_feedback_norm_sq_mean (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (r : ℝ≥0) (hr : r≤1) :
    (∫sample,‖vectorMeasureFeedbackControl (n:=n) μ β t ht r sample‖^2∂vectorMeasureDisorderTilt μ β t a)=
      (n:ℝ)*vectorMeanOverlap (n:=n) μ β t a ht ⟨r,⟨r.coe_nonneg,hr⟩⟩ := by
  simp_rw [EuclideanSpace.real_norm_sq_eq,vectorMeasureFeedbackControl_eq_spinMean μ β t ht r hr]
  rw [integral_finsetSum _ (fun l _=>by
    simpa only [pow_two] using integrable_vectorMeanOverlap_mul μ β t a ht _ _ l)]
  unfold vectorMeanOverlap
  by_cases hn : n=0
  · subst n
    simp
  · field_simp

end QuantitativeFollowup
