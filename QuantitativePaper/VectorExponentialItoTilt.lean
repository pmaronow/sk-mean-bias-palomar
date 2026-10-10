module
public import QuantitativePaper.VectorItoIntervalExpectation
public import QuantitativePaper.VectorActualExponentialTime
public import QuantitativePaper.VectorTiltedIntegral
public import FourPapersCommon.BoundedTimeInterval

@[expose] public section

/-! Genuine bounded-test Dynkin identities under the actual unbounded
fractional disorder tilt, proved by truncating its initial density. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n k : ℕ} {T : ℝ≥0}

theorem vector_ito_interval_finiteTilt
    (s : RSBScheme k) (β t outer : ℝ)
    {X d : ℝ≥0→VectorDisorderBrownianSample n→Field n} {σ : ℝ}
    (hc : VectorItoCharacteristics X d σ)
    (test : TimeFTCData (VectorDisorderBrownianSample n) (Field n) T)
    (hf : VectorSpatialItoTest (fun q=>test.f q) X)
    (M : ℝ) (hM : ∀q sample x,‖test.f q sample x‖≤M)
    (a b : ℝ≥0) (hab : a≤b) (hb : b≤T) :
    (∫sample,test.f b sample (X b sample)-test.f a sample (X a sample)
      ∂vectorFiniteDisorderTilt s β t outer)=
    ∫sample,(∫r in Ioc a b,vectorItoGenerator test X d σ r sample
      ∂nonnegativeLebesgueMeasure) ∂vectorFiniteDisorderTilt s β t outer := by
  let P:=vectorDisorderBrownianMeasure n
  let W : VectorDisorderBrownianSample n→ℝ:=fun sample=>
    Real.exp (outer*vectorRecursion s β t sample.1 (k+2) 0)
  have hWpast : Measurable[vectorBrownianFiltration n 0] W :=
    (Real.measurable_exp.comp (measurable_const.mul
      ((measurable_vectorRecursion s β t (k+2)).comp
        (measurable_id.prodMk measurable_const)))).comp
      (stronglyMeasurable_initialVectorDisorder n 0).measurable
  have hWm : Measurable W:=hWpast.mono ((vectorBrownianFiltration n).le 0) le_rfl
  have hWn : ∀sample,0≤W sample:=fun _=>(Real.exp_pos _).le
  have hWi : Integrable W P:=by
    have hi:=integrable_exp_vectorRecursion_add_norm (n:=n) s β t outer 0
    simp only [zero_mul,add_zero] at hi
    exact hi.comp_fst (vectorBrownianMeasure n)
  let F : VectorDisorderBrownianSample n→ℝ:=fun sample=>
    test.f b sample (X b sample)-test.f a sample (X a sample)
  have hFm : Measurable F:=by
    have hr (r : ℝ≥0) : Measurable (fun sample=>test.f r sample (X r sample)) := by
      exact (test.f_measurable.comp (measurable_const.prodMk
        (measurable_id.prodMk (hc.measurable_state.of_uncurry_left)) ))
    exact (hr b).sub (hr a)
  have hFb : ∀sample,‖F sample‖≤M+M:=fun sample=>
    (norm_sub_le _ _).trans (add_le_add (hM b sample _) (hM a sample _))
  obtain ⟨D,hD⟩:=hc.bounded_drift
  let K : ℝ:=hf.firstBound*D+σ^2/2*((n : ℝ)*hf.secondBound)+test.bound
  have hK : 0≤K:=by dsimp [K];positivity
  let G : ℝ≥0→VectorDisorderBrownianSample n→ℝ:=fun r sample=>
    if r∈Ioc a b then vectorItoGenerator test X d σ r sample else 0
  have hGm : Measurable (Function.uncurry G):=by
    exact Measurable.ite (measurableSet_Ioc.preimage measurable_fst)
      (measurable_vectorItoGenerator hc test hf) measurable_const
  have hGb : ∀r sample,‖G r sample‖≤K:=by
    intro r sample
    by_cases hr : r∈Ioc a b
    · simp only [G,if_pos hr]
      exact vectorItoGenerator_bound hc test hf D hD r ⟨r.coe_nonneg,hr.2.trans hb⟩ sample
    · simp only [G,if_neg hr,norm_zero]
      exact hK
  let H : VectorDisorderBrownianSample n→ℝ:=fun sample=>
    ∫r in Ioc a b,G r sample ∂nonnegativeLebesgueMeasure
  have hHm : Measurable H:=measurable_nnreal_intervalIntegral G hGm a b
  have hHb : ∀sample,‖H sample‖≤K*max ((b:ℝ)-a) 0:=
    norm_nnreal_intervalIntegral_le G a b K hGb
  have hHeq (sample : VectorDisorderBrownianSample n) :
      H sample=∫r in Ioc a b,vectorItoGenerator test X d σ r sample
        ∂nonnegativeLebesgueMeasure := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    simp only [G,if_pos hr]
  have he : (∫sample,W sample*F sample ∂P)=∫sample,W sample*H sample ∂P:=by
    apply integral_eq_of_truncated_weight_identity P F H W hFm hHm
      (M+M) (K*max ((b:ℝ)-a) 0) hFb hHb hWm hWn hWi
    intro j
    have hZ : Measurable[vectorBrownianFiltration n 0] (truncateWeight W j):=
      measurable_const.min hWpast
    have hh:=(vector_ito_interval_generator hc test hf (truncateWeight W j) hZ
      (j:ℝ≥0) (norm_truncateWeight_le W hWn j) a b hab hb).2
    change (∫sample,truncateWeight W j sample*F sample ∂P)=_
    rw [hh]
    apply integral_congr_ae
    exact .of_forall fun sample=>by
      dsimp only
      rw [hHeq,integral_const_mul]
  rw [integral_vectorFiniteDisorderTilt,integral_vectorFiniteDisorderTilt]
  apply congrArg (fun z=>z/vectorOuterPartition (n:=n) s β t outer)
  change (∫sample,W sample*F sample ∂P)=_
  rw [he]
  apply integral_congr_ae
  exact .of_forall fun sample=>by
    dsimp only
    rw [hHeq]

end QuantitativePaper
