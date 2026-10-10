module
public import QuantitativePaper.VectorExponentialItoTilt

@[expose] public section

/-! Dominated passage from genuine bounded Dynkin tests to exponential
growth observables along the actual finite-profile tilted diffusion. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vector_finiteTilt_dynkin_of_exponential_localizations
    (s : RSBScheme k) (β t outer : ℝ) (ht : t≤1)
    (tests : ℕ→TimeFTCData (VectorDisorderBrownianSample n) (Field n) 1)
    (hsp : ∀j,VectorSpatialItoTest (fun q=>(tests j).f q) (vectorFiniteState s β t ht))
    (M : ℕ→ℝ) (hM : ∀j q sample x,‖(tests j).f q sample x‖≤M j)
    (f : ℝ≥0→VectorDisorderBrownianSample n→ℝ)
    (G : ℝ≥0→VectorDisorderBrownianSample n→ℝ)
    (hGm : Measurable (Function.uncurry G))
    (a b : ℝ≥0) (hab : a≤b) (hb : b≤1)
    (C K : ℝ) (hC : 0≤C)
    (hFbound : ∀(j : ℕ) (r : ℝ≥0),r≤1→∀sample,
      ‖(tests j).f r sample (vectorFiniteState s β t ht r sample)‖≤
        C*Real.exp (K*(‖sample.1‖+‖vectorFiniteState s β t ht r sample‖)))
    (hFpoint : ∀r : ℝ≥0,r≤1→∀sample,Tendsto
      (fun j=>(tests j).f r sample (vectorFiniteState s β t ht r sample)) atTop (𝓝 (f r sample)))
    (hGbound : ∀j r,r∈Ioc a b→∀sample,
      ‖vectorItoGenerator (tests j) (vectorFiniteState s β t ht)
        (vectorAdditiveDrift (vectorFiniteDriftData s β t ht)
          (Real.sqrt ((1-t)*β^2)) 0 1) (Real.sqrt ((1-t)*β^2)) r sample‖≤
        C*Real.exp (K*(‖sample.1‖+‖vectorFiniteState s β t ht r sample‖)))
    (hGpoint : ∀r,r∈Ioc a b→∀sample,Tendsto
      (fun j=>vectorItoGenerator (tests j) (vectorFiniteState s β t ht)
        (vectorAdditiveDrift (vectorFiniteDriftData s β t ht)
          (Real.sqrt ((1-t)*β^2)) 0 1) (Real.sqrt ((1-t)*β^2)) r sample)
      atTop (𝓝 (G r sample))) :
    Integrable (Function.uncurry G)
      ((nonnegativeLebesgueMeasure.restrict (Ioc a b)).prod (vectorFiniteDisorderTilt s β t outer)) ∧
    (∫sample,f b sample-f a sample ∂vectorFiniteDisorderTilt s β t outer)=
      ∫sample,(∫r in Ioc a b,G r sample ∂nonnegativeLebesgueMeasure)
        ∂vectorFiniteDisorderTilt s β t outer := by
  let P:=vectorFiniteDisorderTilt (n:=n) s β t outer
  letI:=vectorFiniteDisorderTilt_probability (n:=n) s β t outer
  let ν:=nonnegativeLebesgueMeasure.restrict (Ioc a b)
  let X:=vectorFiniteState (n:=n) s β t ht
  let d:=vectorAdditiveDrift (vectorFiniteDriftData (n:=n) s β t ht)
    (Real.sqrt ((1-t)*β^2)) 0 1
  let σ:=Real.sqrt ((1-t)*β^2)
  have hc:=vectorItoCharacteristics_vectorFiniteState (n:=n) s β t ht
  let E : ℝ≥0→VectorDisorderBrownianSample n→ℝ:=fun r sample=>
    C*Real.exp (K*(‖sample.1‖+‖X r sample‖))
  have hEi (r : ℝ≥0) (hr : r≤1) : Integrable (E r) P:=
    (integrable_exp_vectorFiniteState_and_disorder s β t outer K ht r hr).const_mul C
  have hSub : Ioc a b⊆Ioc (0:ℝ≥0) 1:=fun r hr=>⟨lt_of_le_of_lt bot_le hr.1,hr.2.trans hb⟩
  have hTime : Integrable (Function.uncurry E) (ν.prod P):=by
    apply ((integrable_time_exp_vectorFiniteState_and_disorder s β t outer K ht).const_mul C).mono_measure
    exact Measure.prod_mono (Measure.restrict_mono_set _ hSub) le_rfl
  have hMem : ∀ᵐz ∂ν.prod P,z.1∈Ioc a b:=by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact .of_forall fun _=>hr
  let Gj : ℕ→ℝ≥0→VectorDisorderBrownianSample n→ℝ:=fun j=>
    vectorItoGenerator (tests j) X d σ
  have hGjm (j : ℕ) : Measurable (Function.uncurry (Gj j)):=
    measurable_vectorItoGenerator hc (tests j) (hsp j)
  have hGjb (j : ℕ) : ∀ᵐz ∂ν.prod P,‖Gj j z.1 z.2‖≤E z.1 z.2:=by
    filter_upwards [hMem] with z hz
    exact hGbound j z.1 hz z.2
  have hGji (j : ℕ) : Integrable (Function.uncurry (Gj j)) (ν.prod P):=
    hTime.mono' (hGjm j).aestronglyMeasurable (hGjb j)
  have hGi : Integrable (Function.uncurry G) (ν.prod P):=by
    apply hTime.mono' hGm.aestronglyMeasurable
    filter_upwards [hMem] with z hz
    exact le_of_tendsto ((hGpoint z.1 hz z.2).norm) (.of_forall fun j=>hGbound j z.1 hz z.2)
  have hRight : Tendsto (fun j=>∫z,Gj j z.1 z.2 ∂ν.prod P) atTop
      (𝓝 (∫z,G z.1 z.2 ∂ν.prod P)):=by
    apply tendsto_integral_of_dominated_convergence (Function.uncurry E)
      (fun j=>(hGjm j).aestronglyMeasurable) hTime hGjb
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
    rw [vector_ito_interval_finiteTilt s β t outer hc (tests j) (hsp j) (M j) (hM j) a b hab hb]
    exact ((integral_prod _ (hGji j)).trans (integral_integral_swap (hGji j))).symm
  have hEq:=tendsto_nhds_unique hLeft (hRight.congr (fun j=>(he j).symm))
  refine ⟨hGi,?_⟩
  exact hEq.trans ((integral_prod _ hGi).trans (integral_integral_swap hGi))

end QuantitativePaper
