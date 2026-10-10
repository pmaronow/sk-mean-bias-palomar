module
public import QuantitativePaper.VectorRestartExponentialEnvelope
public import QuantitativePaper.VectorItoIntervalExpectation
public import QuantitativePaper.VectorExponentialItoGenerator

@[expose] public section

/-! Dominated passage from genuine bounded Dynkin tests to exponential
growth observables along the actual fixed-disorder, fixed-field restarted diffusion. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 4000
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vector_restart_dynkin_of_exponential_localizations
    (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n)
    (tests : ℕ→TimeFTCData (VectorDisorderBrownianSample n) (Field n) 1)
    (hsp : ∀j,VectorSpatialItoTest (fun q=>(tests j).f q) (vectorRestartState μ β t ht q p x))
    (f : ℝ≥0→VectorDisorderBrownianSample n→ℝ)
    (G : ℝ≥0→VectorDisorderBrownianSample n→ℝ)
    (hGm : Measurable (Function.uncurry G))
    (a b : ℝ≥0) (hab : a≤b) (hb : b≤1)
    (C K : ℝ) (hC : 0≤C)
    (hFbound : ∀(j : ℕ) (r : ℝ≥0),r≤1→∀sample,
      ‖(tests j).f r sample (vectorRestartState μ β t ht q p x r sample)‖≤
        C*Real.exp (K*(‖sample.1‖+‖vectorRestartState μ β t ht q p x r sample‖)))
    (hFpoint : ∀r : ℝ≥0,r≤1→∀sample,Tendsto
      (fun j=>(tests j).f r sample (vectorRestartState μ β t ht q p x r sample)) atTop (𝓝 (f r sample)))
    (hGbound : ∀j r,r∈Ioc a b→∀sample,
      ‖vectorItoGenerator (tests j) (vectorRestartState μ β t ht q p x)
        (vectorAdditiveDrift (vectorRestartDriftData μ β t ht q p)
          (Real.sqrt ((1-t)*β^2)) x (vectorRestartHorizon q)) (Real.sqrt ((1-t)*β^2)) r sample‖≤
        C*Real.exp (K*(‖sample.1‖+‖vectorRestartState μ β t ht q p x r sample‖)))
    (hGpoint : ∀r,r∈Ioc a b→∀sample,Tendsto
      (fun j=>vectorItoGenerator (tests j) (vectorRestartState μ β t ht q p x)
        (vectorAdditiveDrift (vectorRestartDriftData μ β t ht q p)
          (Real.sqrt ((1-t)*β^2)) x (vectorRestartHorizon q)) (Real.sqrt ((1-t)*β^2)) r sample)
      atTop (𝓝 (G r sample))) :
    Integrable (Function.uncurry G)
      ((nonnegativeLebesgueMeasure.restrict (Ioc a b)).prod (vectorDisorderBrownianMeasure n)) ∧
    (∫sample,f b sample-f a sample ∂vectorDisorderBrownianMeasure n)=
      ∫sample,(∫r in Ioc a b,G r sample ∂nonnegativeLebesgueMeasure)
        ∂vectorDisorderBrownianMeasure n := by
  let P:=vectorDisorderBrownianMeasure n
  let ν:=nonnegativeLebesgueMeasure.restrict (Ioc a b)
  let X:=vectorRestartState (n:=n) μ β t ht q p x
  let d:=vectorAdditiveDrift (vectorRestartDriftData (n:=n) μ β t ht q p)
    (Real.sqrt ((1-t)*β^2)) x (vectorRestartHorizon q)
  let σ:=Real.sqrt ((1-t)*β^2)
  have hc:=vectorItoCharacteristics_vectorRestartState (n:=n) μ β t ht q p x
  let E : ℝ≥0→VectorDisorderBrownianSample n→ℝ:=fun r sample=>
    C*Real.exp (K*(‖sample.1‖+‖X r sample‖))
  let V : VectorDisorderBrownianSample n→ℝ:=fun sample=>
    C*vectorRestartExponentialEnvelope β t K x sample
  have hVi : Integrable V P:=(integrable_vectorRestartExponentialEnvelope β t K x).const_mul C
  have hEv (r : ℝ≥0) (hr : r≤1) (sample : VectorDisorderBrownianSample n) :
      E r sample≤V sample := mul_le_mul_of_nonneg_left
    (exp_vectorRestartState_and_disorder_le_envelope μ β t K ht q p x r hr sample) hC
  have hEi (r : ℝ≥0) (hr : r≤1) : Integrable (E r) P := by
    have hEm : Measurable (E r) :=
      ((measurable_fst.norm.add hc.measurable_state.of_uncurry_left.norm).const_mul K).exp.const_mul C
    apply hVi.mono' hEm.aestronglyMeasurable
    exact .of_forall fun sample=>by
      have hn : 0≤E r sample:=mul_nonneg hC (Real.exp_pos _).le
      rw [Real.norm_of_nonneg hn]
      exact hEv r hr sample
  have : IsFiniteMeasure ν:=⟨by
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.mpr (nonnegativeLebesgueMeasure_Ioc_ne_top a b)⟩
  have hTime : Integrable (fun z : ℝ≥0×VectorDisorderBrownianSample n=>V z.2) (ν.prod P):=
    hVi.comp_snd ν
  have hMem : ∀ᵐz ∂ν.prod P,z.1∈Ioc a b:=by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact .of_forall fun _=>hr
  let Gj : ℕ→ℝ≥0→VectorDisorderBrownianSample n→ℝ:=fun j=>
    vectorItoGenerator (tests j) X d σ
  have hGjm (j : ℕ) : Measurable (Function.uncurry (Gj j)):=
    measurable_vectorItoGenerator hc (tests j) (hsp j)
  have hGji (j : ℕ) : Integrable (Function.uncurry (Gj j)) (ν.prod P):=
    hTime.mono' (hGjm j).aestronglyMeasurable ((by
      filter_upwards [hMem] with z hz
      exact (hGbound j z.1 hz z.2).trans (hEv z.1 (hz.2.trans hb) z.2)))
  have hGi : Integrable (Function.uncurry G) (ν.prod P):=by
    apply hTime.mono' hGm.aestronglyMeasurable
    filter_upwards [hMem] with z hz
    exact le_of_tendsto ((hGpoint z.1 hz z.2).norm) (.of_forall fun j=>(hGbound j z.1 hz z.2).trans (hEv z.1 (hz.2.trans hb) z.2))
  have hRight : Tendsto (fun j=>∫z,Gj j z.1 z.2 ∂ν.prod P) atTop
      (𝓝 (∫z,G z.1 z.2 ∂ν.prod P)):=by
    apply tendsto_integral_of_dominated_convergence (fun z : ℝ≥0×VectorDisorderBrownianSample n=>V z.2)
      (fun j=>(hGjm j).aestronglyMeasurable) hTime
      (fun j=>by
        filter_upwards [hMem] with z hz
        exact (hGbound j z.1 hz z.2).trans (hEv z.1 (hz.2.trans hb) z.2))
    filter_upwards [hMem] with z hz
    exact hGpoint z.1 hz z.2
  have hLeft : Tendsto (fun j=>∫sample,
      (tests j).f b sample (X b sample)-(tests j).f a sample (X a sample) ∂P)
      atTop (𝓝 (∫sample,f b sample-f a sample ∂P)):=by
    apply tendsto_integral_of_dominated_convergence (fun sample=>E b sample+E a sample)
    · intro j
      have hm (r : ℝ≥0) : Measurable (fun sample=>(tests j).f r sample (X r sample)):=
        (tests j).f_measurable.comp (measurable_const.prodMk
          (measurable_id.prodMk hc.measurable_state.of_uncurry_left))
      exact ((hm b).sub (hm a)).aestronglyMeasurable
    · exact (hEi b hb).add (hEi a (hab.trans hb))
    · intro j
      exact .of_forall fun sample=>(norm_sub_le _ _).trans
        (add_le_add (hFbound j b hb sample) (hFbound j a (hab.trans hb) sample))
    · exact .of_forall fun sample=>(hFpoint b hb sample).sub (hFpoint a (hab.trans hb) sample)
  have he (j : ℕ) : (∫sample,(tests j).f b sample (X b sample)-(tests j).f a sample (X a sample) ∂P)=
      ∫z,Gj j z.1 z.2 ∂ν.prod P:=by
    have hi:=vector_ito_interval_generator hc (tests j) (hsp j)
      (fun _=>1) measurable_const 1 (fun _=>by norm_num) a b hab hb
    have hh : (∫sample,(tests j).f b sample (X b sample)-(tests j).f a sample (X a sample) ∂P)=
        ∫sample,(∫r in Ioc a b,Gj j r sample∂nonnegativeLebesgueMeasure)∂P := by
      simpa only [one_mul] using hi.2
    exact hh.trans ((integral_prod _ (hGji j)).trans (integral_integral_swap (hGji j))).symm
  have hEq:=tendsto_nhds_unique hLeft (hRight.congr (fun j=>(he j).symm))
  refine ⟨hGi,?_⟩
  exact hEq.trans ((integral_prod _ hGi).trans (integral_integral_swap hGi))

end QuantitativePaper
