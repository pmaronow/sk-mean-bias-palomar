module
public import HexagonPaper.PathHeatSectionwiseWienerModel
public import HexagonPaper.PathHeatSectionwiseWienerLimit
public import HexagonPaper.PathHeatClockCompactBound

@[expose] public section

/-! Actual common-Wiener normalized moments for sectionwise signed sources.
Only the active coordinates and the parameter vary in the continuity proofs;
the sampled Gaussian and finite auxiliaries are fixed in each section.
The common envelopes and measurability are derived from the analytic source,
not supplied as normalized-moment or domination conclusions. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped Topology BigOperators unitInterval NNReal BoundedContinuousFunction
namespace HexagonPaper
set_option maxHeartbeats 250000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Fintype K] [Nonempty K] [TopologicalSpace K] [DiscreteTopology K]
  [MeasurableSpace K] [BorelSpace K] [MeasurableSingletonClass K]
variable {L : ℕ} {a b : ℝ}

variable (μ : Measure E)
  (d : PathHeatSectionwiseSignedSource (Icc a b) E K (Fin L×I))
  (c : Icc a b→Fin L→C(I,I)) (dc : Icc a b→Fin L→C(I,ℝ))
  (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)

def pathHeatSectionwiseWienerApproximateNormalizer (n : ℕ) (z : Icc a b) : ℝ :=
  pathHeatNormalizer (pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ)
    (fun ω=>d.weight (pathHeatWienerSourceApproximateState L c (pathHeatTreeMixedOperator δ W) n z ω))

def pathHeatSectionwiseWienerApproximateExpectation (n : ℕ) (z : Icc a b) : ℝ :=
  pathHeatExpectation (pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ)
    (fun ω=>d.weight (pathHeatWienerSourceApproximateState L c (pathHeatTreeMixedOperator δ W) n z ω))
    (fun ω=>d.phi (pathHeatWienerSourceApproximateState L c (pathHeatTreeMixedOperator δ W) n z ω))

def pathHeatSectionwiseWienerApproximateResponse (n : ℕ) (z : Icc a b) : ℝ :=
  pathHeatResponse (pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ)
    (fun ω=>d.weight (pathHeatWienerSourceApproximateState L c (pathHeatTreeMixedOperator δ W) n z ω))
    (fun ω=>d.phi (pathHeatWienerSourceApproximateState L c (pathHeatTreeMixedOperator δ W) n z ω))
    (fun ω=>d.densityGenerator (pathHeatWienerSourceApproximateKernel L (pathHeatTreeMixedKernelOperator δ W)
      (fun z=>pathHeatClockRawKernel (dc z)) n z) (pathHeatWienerSourceApproximateState L c (pathHeatTreeMixedOperator δ W) n z ω))
    (fun ω=>d.observableGenerator (pathHeatWienerSourceApproximateKernel L (pathHeatTreeMixedKernelOperator δ W)
      (fun z=>pathHeatClockRawKernel (dc z)) n z) (pathHeatWienerSourceApproximateState L c (pathHeatTreeMixedOperator δ W) n z ω))

def pathHeatSectionwiseWienerApproximateLogNormalizerResponse (n : ℕ) (z : Icc a b) : ℝ :=
  pathHeatExpectation (pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ)
    (fun ω=>d.weight (pathHeatWienerSourceApproximateState L c (pathHeatTreeMixedOperator δ W) n z ω))
    (fun ω=>d.densityGenerator (pathHeatWienerSourceApproximateKernel L (pathHeatTreeMixedKernelOperator δ W)
      (fun z=>pathHeatClockRawKernel (dc z)) n z) (pathHeatWienerSourceApproximateState L c (pathHeatTreeMixedOperator δ W) n z ω))

variable [IsGaussian μ]

theorem pathHeatSectionwiseWiener_positive_normalizer (hab : a≤b)
    (C : ℝ≥0) (hs : PathHeatSectionwiseAnalyticSource a b hab d C) (z : Icc a b) :
    0<pathHeatSectionwiseWienerNormalizer μ d c δ W z := by
  let dc₀ : Icc a b→Fin L→C(I,ℝ) := fun _ _=>0
  obtain ⟨κ,hκ⟩ := exists_pathHeatClockRawKernel_bound_of_continuous dc₀ (fun _=>continuous_const)
  exact pathHeat_normalizer_positive
    (pathHeatSectionwiseWiener_actual_dominatedData μ hab d C hs c δ W
      (fun z=>pathHeatClockRawKernel (dc₀ z)) κ hκ z)

theorem pathHeatSectionwiseWiener_continuous_moments_of_bound (hab : a≤b)
    (C : ℝ≥0) (hs : PathHeatSectionwiseAnalyticSource a b hab d C)
    (κ : ℝ≥0) (hκ : ∀z,‖pathHeatClockRawKernel (dc z)‖≤κ)
    (hc : ∀l,Continuous (fun z=>c z l)) (hdc : ∀l,Continuous (fun z=>dc z l)) :
    (∀z,0<pathHeatSectionwiseWienerNormalizer μ d c δ W z) ∧
    Continuous (pathHeatSectionwiseWienerNormalizer μ d c δ W) ∧
    Continuous (pathHeatSectionwiseWienerExpectation μ d c δ W) ∧
    Continuous (pathHeatSectionwiseWienerResponse μ d c dc δ W) ∧
    Continuous (pathHeatSectionwiseWienerLogNormalizerResponse μ d c dc δ W) := by
  letI : Nonempty (Icc a b) := ⟨⟨a,le_rfl,hab⟩⟩
  let T : C(Fin L×I,ℝ)→L[ℝ]C(Fin L×I,ℝ) := pathHeatTreeMixedOperator δ W
  let A : C(Fin L×I,C(Fin L×I,ℝ))→L[ℝ]C(Fin L×I,C(Fin L×I,ℝ)) := pathHeatTreeMixedKernelOperator δ W
  let D := fun z=>pathHeatClockRawKernel (dc z)
  let p := fun (z : Icc a b) (ω : pathHeatGeneralBaseSample E (Fin L) K)=>
    T (pathHeatFlatClockPath L (c z) ω.1.2)
  have hp (ω : pathHeatGeneralBaseSample E (Fin L) K) : Continuous (fun z=>p z ω) :=
    T.continuous.comp (continuous_pathHeatFlatClockPath_family L c (fun _=>ω.1.2) hc (fun _=>continuous_const))
  have hkernel := continuous_pathHeatWienerSourceKernel L A D (continuous_pathHeatRawClockKernel_family dc hdc)
  exact pathHeat_sections_normalized_continuity
    (pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ) (fun aux=>d.section aux)
    (fun ω : pathHeatGeneralBaseSample E (Fin L) K=>(ω.1.1,ω.2)) p
    (pathHeatWienerSourceKernel L A D)
    (pathHeatGeneralEnvelope (C*(1+‖T‖))) d.B
    (d.densityBound (pathHeatWienerMixedKernelBound δ W*κ))
    (d.observableBound (pathHeatWienerMixedKernelBound δ W*κ))
    (fun z=>pathHeatSectionwiseWiener_actual_dominatedData μ hab d C hs c δ W D κ hκ z)
    (.of_forall hp) hkernel

theorem pathHeatSectionwiseWiener_continuous_moments (hab : a≤b)
    (C : ℝ≥0) (hs : PathHeatSectionwiseAnalyticSource a b hab d C)
    (hc : ∀l,Continuous (fun z=>c z l)) (hdc : ∀l,Continuous (fun z=>dc z l)) :
    (∀z,0<pathHeatSectionwiseWienerNormalizer μ d c δ W z) ∧
    Continuous (pathHeatSectionwiseWienerNormalizer μ d c δ W) ∧
    Continuous (pathHeatSectionwiseWienerExpectation μ d c δ W) ∧
    Continuous (pathHeatSectionwiseWienerResponse μ d c dc δ W) ∧
    Continuous (pathHeatSectionwiseWienerLogNormalizerResponse μ d c dc δ W) := by
  obtain ⟨κ,hκ⟩ := exists_pathHeatClockRawKernel_bound_of_continuous dc hdc
  exact pathHeatSectionwiseWiener_continuous_moments_of_bound μ d c dc δ W hab C hs κ hκ hc hdc

theorem pathHeatSectionwiseWiener_moving_normalized_limits_of_bound (hab : a≤b)
    (C : ℝ≥0) (hs : PathHeatSectionwiseAnalyticSource a b hab d C)
    (κ : ℝ≥0) (hκ : ∀z,‖pathHeatClockRawKernel (dc z)‖≤κ)
    (hc : ∀l,Continuous (fun z=>c z l)) (hdc : ∀l,Continuous (fun z=>dc z l))
    (z : ℕ→Icc a b) (z₀ : Icc a b) (hz : Tendsto z atTop (𝓝 z₀)) :
    0<pathHeatSectionwiseWienerNormalizer μ d c δ W z₀ ∧
    Tendsto (fun n=>pathHeatSectionwiseWienerApproximateNormalizer μ d c δ W n (z n)) atTop
      (𝓝 (pathHeatSectionwiseWienerNormalizer μ d c δ W z₀)) ∧
    Tendsto (fun n=>pathHeatSectionwiseWienerApproximateExpectation μ d c δ W n (z n)) atTop
      (𝓝 (pathHeatSectionwiseWienerExpectation μ d c δ W z₀)) ∧
    Tendsto (fun n=>pathHeatSectionwiseWienerApproximateResponse μ d c dc δ W n (z n)) atTop
      (𝓝 (pathHeatSectionwiseWienerResponse μ d c dc δ W z₀)) ∧
    Tendsto (fun n=>pathHeatSectionwiseWienerApproximateLogNormalizerResponse μ d c dc δ W n (z n)) atTop
      (𝓝 (pathHeatSectionwiseWienerLogNormalizerResponse μ d c dc δ W z₀)) := by
  let D := fun z=>pathHeatClockRawKernel (dc z)
  have h := pathHeatSectionwiseWiener_actual_dominatedData μ hab d C hs c δ W D κ hκ z₀
  have hn := fun n=>pathHeatSectionwiseWiener_approximate_dominatedData μ hab d C hs c δ W D κ hκ n (z n)
  have hv := fun ω=>pathHeatSectionwiseWiener_moving_values d c δ W D hc
    (continuous_pathHeatRawClockKernel_family dc hdc) z z₀ hz ω
  have ht := pathHeat_normalized_limits hn h
    (.of_forall (fun ω=>(hv ω).1)) (.of_forall (fun ω=>(hv ω).2.1))
    (.of_forall (fun ω=>(hv ω).2.2.1)) (.of_forall (fun ω=>(hv ω).2.2.2))
  have hIH := pathHeat_tendsto_weighted_integral h.integrable_envelope h.nonneg_C
    (fun n=>(hn n).weight_measurable) (fun n=>(hn n).density_generator_measurable)
    (fun n=>(hn n).weight_positive) (fun n=>(hn n).weight_bound)
    (fun n=>(hn n).density_generator_bound)
    (.of_forall (fun ω=>(hv ω).1)) (.of_forall (fun ω=>(hv ω).2.2.1))
  exact ⟨ht.1,ht.2.1,ht.2.2.1,ht.2.2.2,hIH.div ht.2.1 ht.1.ne'⟩

theorem pathHeatSectionwiseWiener_moving_normalized_limits (hab : a≤b)
    (C : ℝ≥0) (hs : PathHeatSectionwiseAnalyticSource a b hab d C)
    (hc : ∀l,Continuous (fun z=>c z l)) (hdc : ∀l,Continuous (fun z=>dc z l))
    (z : ℕ→Icc a b) (z₀ : Icc a b) (hz : Tendsto z atTop (𝓝 z₀)) :
    0<pathHeatSectionwiseWienerNormalizer μ d c δ W z₀ ∧
    Tendsto (fun n=>pathHeatSectionwiseWienerApproximateNormalizer μ d c δ W n (z n)) atTop
      (𝓝 (pathHeatSectionwiseWienerNormalizer μ d c δ W z₀)) ∧
    Tendsto (fun n=>pathHeatSectionwiseWienerApproximateExpectation μ d c δ W n (z n)) atTop
      (𝓝 (pathHeatSectionwiseWienerExpectation μ d c δ W z₀)) ∧
    Tendsto (fun n=>pathHeatSectionwiseWienerApproximateResponse μ d c dc δ W n (z n)) atTop
      (𝓝 (pathHeatSectionwiseWienerResponse μ d c dc δ W z₀)) ∧
    Tendsto (fun n=>pathHeatSectionwiseWienerApproximateLogNormalizerResponse μ d c dc δ W n (z n)) atTop
      (𝓝 (pathHeatSectionwiseWienerLogNormalizerResponse μ d c dc δ W z₀)) := by
  obtain ⟨κ,hκ⟩ := exists_pathHeatClockRawKernel_bound_of_continuous dc hdc
  exact pathHeatSectionwiseWiener_moving_normalized_limits_of_bound μ d c dc δ W hab C hs κ hκ hc hdc z z₀ hz

theorem pathHeatSectionwiseWiener_moving_normalized_limits_succ (hab : a≤b)
    (C : ℝ≥0) (hs : PathHeatSectionwiseAnalyticSource a b hab d C)
    (hc : ∀l,Continuous (fun z=>c z l)) (hdc : ∀l,Continuous (fun z=>dc z l))
    (z : ℕ→Icc a b) (z₀ : Icc a b) (hz : Tendsto z atTop (𝓝 z₀)) :
    0<pathHeatSectionwiseWienerNormalizer μ d c δ W z₀ ∧
    Tendsto (fun n=>pathHeatSectionwiseWienerApproximateNormalizer μ d c δ W (n+1) (z n)) atTop
      (𝓝 (pathHeatSectionwiseWienerNormalizer μ d c δ W z₀)) ∧
    Tendsto (fun n=>pathHeatSectionwiseWienerApproximateExpectation μ d c δ W (n+1) (z n)) atTop
      (𝓝 (pathHeatSectionwiseWienerExpectation μ d c δ W z₀)) ∧
    Tendsto (fun n=>pathHeatSectionwiseWienerApproximateResponse μ d c dc δ W (n+1) (z n)) atTop
      (𝓝 (pathHeatSectionwiseWienerResponse μ d c dc δ W z₀)) ∧
    Tendsto (fun n=>pathHeatSectionwiseWienerApproximateLogNormalizerResponse μ d c dc δ W (n+1) (z n)) atTop
      (𝓝 (pathHeatSectionwiseWienerLogNormalizerResponse μ d c dc δ W z₀)) := by
  have hv := pathHeatSectionwiseWiener_moving_normalized_limits μ d c dc δ W hab C hs hc hdc
    (fun n=>z (n-1)) z₀ (hz.comp (tendsto_sub_atTop_nat 1))
  refine ⟨hv.1,?_,?_,?_,?_⟩
  · simpa only [Function.comp_def,Nat.add_sub_cancel] using hv.2.1.comp (tendsto_add_atTop_nat 1)
  · simpa only [Function.comp_def,Nat.add_sub_cancel] using hv.2.2.1.comp (tendsto_add_atTop_nat 1)
  · simpa only [Function.comp_def,Nat.add_sub_cancel] using hv.2.2.2.1.comp (tendsto_add_atTop_nat 1)
  · simpa only [Function.comp_def,Nat.add_sub_cancel] using hv.2.2.2.2.comp (tendsto_add_atTop_nat 1)

end HexagonPaper
