module
public import QuantitativeFollowup.VectorAffineIntegrand
public import QuantitativeFollowup.VectorFeedbackPairing
public import QuantitativeFollowup.VectorOverlapDeficit
public import Paper.ParisiCDFIntegral

@[expose] public section

/-! The actual all-profile vector first variation, expressed by the
constructed self-overlap. Terminal pairing, normalization and Fubini are
proved rather than supplied as contact or moment hypotheses. -/
noncomputable section
open Set MeasureTheory QuantitativePaper StochasticCalculus FourPapersCommon
open scoped NNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem integral_vectorAffineDerivativeIntegrand_feedback (μ ν : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (r : ℝ≥0) (hr : r≤1) :
    (∫sample,vectorAffineDerivativeIntegrand μ ν β t
      (vectorMeasureFeedbackControl (n:=n) μ β t ht.le) r sample ∂vectorMeasureDisorderTilt μ β t a)=
      (((1-t)*β^2)*(n:ℝ)/2)*(Paper.parisiCDF ν r-Paper.parisiCDF μ r)*
        vectorMeanOverlapReal (n:=n) μ β t a ht.le r := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht.le
  let P:=vectorMeasureDisorderTilt (n:=n) μ β t a
  let A:=vectorMeasureFeedbackControl (n:=n) μ β t ht.le
  let c:=(1-t)*β^2
  let v:=fun sample : VectorDisorderBrownianSample n=>vectorTerminalGradient n β t sample.1
    (vectorControlledState c μ A 1 sample)
  have hA:=isVectorParisiControl_vectorMeasureFeedbackControl (n:=n) μ β t ht.le
  have hX:=(measurable_vectorControlledState c μ A hA).of_uncurry_left (x:=1)
  have hv:=(continuous_vectorTerminalGradient (n:=n) β t).measurable.comp
    (measurable_fst.prodMk hX)
  have ha:=hA.measurable.of_uncurry_left (x:=r)
  have hbA (sample : VectorDisorderBrownianSample n) : ‖A r sample‖^2≤(n:ℝ):=by
    nlinarith [hA.norm_le r sample,Real.sq_sqrt (Nat.cast_nonneg n),norm_nonneg (A r sample)]
  have hbn (sample : VectorDisorderBrownianSample n) : ‖inner ℝ (v sample) (A r sample)‖≤(n:ℝ):=by
    calc
      _≤‖v sample‖*‖A r sample‖:=norm_inner_le_norm _ _
      _≤Real.sqrt (n:ℝ)*Real.sqrt (n:ℝ):=mul_le_mul
        (norm_vectorTerminalGradient_le β t sample.1 _) (hA.norm_le r sample)
        (norm_nonneg _) (Real.sqrt_nonneg _)
      _=(n:ℝ):=Real.mul_self_sqrt (Nat.cast_nonneg n)
  have hi1 : Integrable (fun sample=>inner ℝ (v sample) (A r sample)) P:=
    (integrable_const (n:ℝ)).mono' (hv.inner ha).aestronglyMeasurable (.of_forall hbn)
  have hi2 : Integrable (fun sample=>‖A r sample‖^2) P:=
    (integrable_const (n:ℝ)).mono' (ha.norm.pow_const 2).aestronglyMeasurable
      (.of_forall fun sample=>by rw [Real.norm_of_nonneg (sq_nonneg _)];exact hbA sample)
  have he:=vector_feedback_terminal_pairing (n:=n) μ β t a hβ ht r hr
  have hm:=vector_feedback_norm_sq_mean (n:=n) μ β t a ht.le r hr
  change (∫sample,inner ℝ (v sample) (A r sample)∂P)=(∫sample,‖A r sample‖^2∂P) at he
  change (∫sample,‖A r sample‖^2∂P)=(n:ℝ)*vectorMeanOverlap (n:=n) μ β t a ht.le ⟨r,⟨r.coe_nonneg,hr⟩⟩ at hm
  change (∫sample,c*(Paper.parisiCDF ν r-Paper.parisiCDF μ r)*
    (inner ℝ (v sample) (A r sample)-‖A r sample‖^2/2)∂P)=_
  rw [integral_const_mul,integral_sub hi1 (hi2.div_const 2),integral_div,he,hm,
    vectorMeanOverlapReal,projIcc_of_mem zero_le_one (show (r:ℝ)∈Icc (0:ℝ) 1 from ⟨r.coe_nonneg,hr⟩)]
  dsimp only [c]
  ring

theorem vectorMeasureFractionalControlDerivative_eq_moment (μ ν : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) :
    vectorMeasureFractionalControlDerivative (n:=n) μ ν β t ht.le a=
      (((1-t)*β^2)*(n:ℝ)/2)*
        ∫r in (0:ℝ)..1,(Paper.parisiCDF ν r-Paper.parisiCDF μ r)*
          vectorMeanOverlapReal (n:=n) μ β t a ht.le r := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht.le
  rw [vectorMeasureFractionalControlDerivative,vectorWeightedMeasureControlDerivative,
    ←integral_vectorMeasureDisorderTilt μ β t a ht.le,
    integral_vectorAffineControlDerivative_eq_time_integral _ μ ν β t _
      (isVectorParisiControl_vectorMeasureFeedbackControl (n:=n) μ β t ht.le)]
  have he : (∫r in Ioc (0:ℝ≥0) 1,
      (∫sample,vectorAffineDerivativeIntegrand μ ν β t (vectorMeasureFeedbackControl (n:=n) μ β t ht.le) r sample
        ∂vectorMeasureDisorderTilt μ β t a)∂nonnegativeLebesgueMeasure)=
      ∫r in Ioc (0:ℝ≥0) 1,((((1-t)*β^2)*(n:ℝ)/2)*
        ((Paper.parisiCDF ν r-Paper.parisiCDF μ r)*vectorMeanOverlapReal (n:=n) μ β t a ht.le r))
        ∂nonnegativeLebesgueMeasure:=by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    dsimp only
    rw [integral_vectorAffineDerivativeIntegrand_feedback (n:=n) μ ν β t a hβ ht r hr.2]
    ring
  rw [he,integral_const_mul]
  congr 1
  exact vectorNonnegativeTimeIntegral_eq_interval _
    (((Paper.parisiCDF_monotone ν).measurable.sub (Paper.parisiCDF_monotone μ).measurable).mul
      (continuous_vectorMeanOverlapReal (n:=n) μ β t a ht.le).measurable) 1


theorem hasDerivWithinAt_vectorMeasureFunctional_mix_moment (hn : 0<n)
    (μ ν : Paper.ParisiMeasure) (β t a : ℝ) (hβ : β≠0) (ht : t<1) :
    HasDerivWithinAt (fun lam=>vectorMeasureFunctional n (Paper.parisiMix μ ν lam) β t a)
      (((1-t)*β^2)/2*∫r in (0:ℝ)..1,(Paper.parisiCDF ν r-Paper.parisiCDF μ r)*
        (vectorMeanOverlapReal (n:=n) μ β t a ht.le r-r)) (Icc (0:ℝ) 1) 0 := by
  have hd:=hasDerivWithinAt_vectorMeasureFunctional_mix_control (n:=n) μ ν β t ht.le a
  rw [vectorMeasureFractionalControlDerivative_eq_moment μ ν β t a hβ ht] at hd
  have hδ:IntervalIntegrable (fun r=>Paper.parisiCDF ν r-Paper.parisiCDF μ r) volume 0 1:=
    (Paper.parisiCDF_intervalIntegrable ν 0 1).sub (Paper.parisiCDF_intervalIntegrable μ 0 1)
  have hiS:IntervalIntegrable (fun r=>(Paper.parisiCDF ν r-Paper.parisiCDF μ r)*
      vectorMeanOverlapReal (n:=n) μ β t a ht.le r) volume 0 1:=
    hδ.mul_continuousOn (continuous_vectorMeanOverlapReal μ β t a ht.le).continuousOn
  have hit:IntervalIntegrable (fun r=>(Paper.parisiCDF ν r-Paper.parisiCDF μ r)*r) volume 0 1:=
    hδ.mul_continuousOn continuous_id.continuousOn
  have hicν:IntervalIntegrable (fun r=>r*Paper.parisiCDF ν r) volume 0 1:=
    (Paper.parisiCDF_intervalIntegrable ν 0 1).continuousOn_mul continuous_id.continuousOn
  have hicμ:IntervalIntegrable (fun r=>r*Paper.parisiCDF μ r) volume 0 1:=
    (Paper.parisiCDF_intervalIntegrable μ 0 1).continuousOn_mul continuous_id.continuousOn
  have hc : (∫r in (0:ℝ)..1,r*Paper.parisiCDF ν r)-(∫r in (0:ℝ)..1,r*Paper.parisiCDF μ r)=
      ∫r in (0:ℝ)..1,(Paper.parisiCDF ν r-Paper.parisiCDF μ r)*r := by
    rw [←intervalIntegral.integral_sub hicν hicμ]
    apply intervalIntegral.integral_congr
    intro r _
    ring
  have he : (∫r in (0:ℝ)..1,(Paper.parisiCDF ν r-Paper.parisiCDF μ r)*
      (vectorMeanOverlapReal (n:=n) μ β t a ht.le r-r))=
      (∫r in (0:ℝ)..1,(Paper.parisiCDF ν r-Paper.parisiCDF μ r)*vectorMeanOverlapReal (n:=n) μ β t a ht.le r)-
      (∫r in (0:ℝ)..1,(Paper.parisiCDF ν r-Paper.parisiCDF μ r)*r) := by
    rw [←intervalIntegral.integral_sub hiS hit]
    apply intervalIntegral.integral_congr
    intro r _
    ring
  rw [hc] at hd
  have hn0 : (n:ℝ)≠0:=Nat.cast_ne_zero.mpr hn.ne'
  convert hd using 1
  rw [he]
  field_simp <;> ring

end QuantitativeFollowup
