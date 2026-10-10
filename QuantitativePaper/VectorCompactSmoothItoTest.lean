module
public import QuantitativePaper.VectorCompactSmoothItoTestJets

@[expose] public section

/-! Compactly supported smooth joint tests yield the actual analytic test
structures used by the vector Brownian Itô proof. The initial disorder is
measurable in the constructed enlarged filtration; no stochastic identity
is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def vectorCompactSmoothSampleTimeData (f : VectorCompactTestParameter n → ℝ)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (T : ℝ≥0) :
    TimeFTCData (VectorDisorderBrownianSample n) (Field n) T := by
  let hbound := hs.exists_bound_iteratedFDeriv hf 3
  let K := Classical.choose hbound
  have hK := (Classical.choose_spec hbound).1
  have hB := (Classical.choose_spec hbound).2
  have hft := contDiff_vectorCompactSmoothTimeField hf
  have hsft := hasCompactSupport_vectorCompactSmoothTimeField hs
  let htbound := hsft.exists_bound_iteratedFDeriv hft 1
  let J := Classical.choose htbound
  have hJ := (Classical.choose_spec htbound).1
  have hJB := (Classical.choose_spec htbound).2
  have hLip : LipschitzWith ⟨J,hJ⟩ (vectorCompactSmoothTimeField f) :=
    lipschitzWith_of_nnnorm_fderiv_le (hft.differentiable (by simp)) (fun z => by
      change ‖fderiv ℝ (vectorCompactSmoothTimeField f) z‖ ≤ J
      rw [← norm_iteratedFDeriv_one]
      exact hJB 1 le_rfl z)
  refine {
    f := fun r sample x => f (r,(sample.1,x))
    ft := fun r sample x => vectorCompactSmoothTimeField f (r,(sample.1,x))
    bound := ⟨K,hK⟩
    spatialLip := ⟨J,hJ⟩
    f_measurable := ?_
    ft_measurable := ?_
    f_continuous := ?_
    derivative := ?_
    ft_continuous := ?_
    ft_bound := ?_
    ft_lipschitz := ?_ }
  · exact hf.continuous.measurable.comp (show Measurable
      (fun z : ℝ×(VectorDisorderBrownianSample n×Field n) =>
        (z.1,(z.2.1.1,z.2.2))) from by fun_prop)
  · exact hft.continuous.measurable.comp (show Measurable
      (fun z : ℝ×(VectorDisorderBrownianSample n×Field n) =>
        (z.1,(z.2.1.1,z.2.2))) from by fun_prop)
  · intro sample x
    exact (hf.continuous.comp (show Continuous (fun r : ℝ => (r,(sample.1,x))) from by fun_prop)).continuousOn
  · intro sample x r _
    exact hasDerivAt_vectorCompactSmooth_time hf r sample.1 x
  · intro sample
    exact hft.continuous.comp (show Continuous (fun z : ℝ×Field n =>
      (z.1,(sample.1,z.2))) from by fun_prop)
  · intro r _ sample x
    have hb : ‖fderiv ℝ f (r,(sample.1,x))‖ ≤ K := by
      rw [←norm_iteratedFDeriv_one]
      exact hB 1 (by omega) _
    have he : ‖((1,(0,0)) : VectorCompactTestParameter n)‖=1 := by simp [Prod.norm_def]
    change ‖fderiv ℝ f (r,(sample.1,x)) (1,(0,0))‖ ≤ K
    calc
      _ ≤ ‖fderiv ℝ f (r,(sample.1,x))‖ * ‖((1,(0,0)) : VectorCompactTestParameter n)‖ :=
        (fderiv ℝ f (r,(sample.1,x))).le_opNorm _
      _ ≤ K := by simpa only [he,mul_one] using hb
  · intro r _ sample
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Prod.dist_eq,dist_self,max_eq_right (dist_nonneg)] using hLip.dist_le_mul (r,(sample.1,x)) (r,(sample.1,y))

def vectorCompactSmoothSampleSpatialTest (f : VectorCompactTestParameter n → ℝ)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
    (X : ℝ≥0 → VectorDisorderBrownianSample n → Field n)
    (hX : ∀ sample,Continuous (fun q => X q sample))
    (hXa : StronglyAdapted (vectorBrownianFiltration n) X) :
    VectorSpatialItoTest (fun q sample x => f (q,(sample.1,x))) X := by
  let hbound := hs.exists_bound_iteratedFDeriv hf 3
  let K := Classical.choose hbound
  have hK := (Classical.choose_spec hbound).1
  have hB := (Classical.choose_spec hbound).2
  have hjet (r : ℝ) (p : Couplings n×ℝ) (x : Field n) (j : ℕ) (hj : j≤3) :
      ‖iteratedFDeriv ℝ j (fun y => f (r,(p,y))) x‖ ≤ K :=
    (norm_iteratedFDeriv_vectorCompactSmooth_section_le hf r p x j).trans (hB j hj _)
  have hfirst := continuous_fderiv_vectorCompactSmooth_section hf
  have hsecond := continuous_vectorHessian_vectorCompactSmooth_section hf
  refine {
    firstBound := ⟨K,hK⟩
    secondBound := ⟨K,hK⟩
    thirdBound := ⟨K,hK⟩
    measurable := ?_
    regularity := ?_
    first_le := ?_
    second_le := ?_
    third_le := ?_
    adapted_first := ?_
    adapted_second := ?_
    continuous_first_path := ?_
    continuous_trace_path := ?_ }
  · intro q
    exact hf.continuous.measurable.comp (show Measurable
      (fun z : VectorDisorderBrownianSample n×Field n => ((q : ℝ),(z.1.1,z.2))) from by fun_prop)
  · intro q sample
    exact (hf.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))).of_le (by simp)
  · intro q sample x
    rw [←norm_iteratedFDeriv_one]
    exact hjet q sample.1 x 1 (by omega)
  · intro q sample x
    exact hjet q sample.1 x 2 (by omega)
  · intro q sample x
    exact hjet q sample.1 x 3 le_rfl
  · intro q r
    exact hfirst.measurable.comp (measurable_const.prodMk
      ((stronglyMeasurable_initialVectorDisorder n r).measurable.prodMk (hXa r).measurable))
  · intro q r
    exact hsecond.measurable.comp (measurable_const.prodMk
      ((stronglyMeasurable_initialVectorDisorder n r).measurable.prodMk (hXa r).measurable))
  · intro sample
    exact hfirst.comp (NNReal.continuous_coe.prodMk (continuous_const.prodMk (hX sample)))
  · intro sample
    have hp : Continuous (fun q : ℝ≥0 => ((q : ℝ),(sample.1,X q sample))) :=
      NNReal.continuous_coe.prodMk (continuous_const.prodMk (hX sample))
    have H := hsecond.comp hp
    unfold vectorBilinearTrace
    apply continuous_finsetSum
    intro i _
    exact (H.clm_apply continuous_const).clm_apply continuous_const

end QuantitativePaper
