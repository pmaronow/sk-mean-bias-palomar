module
public import HexagonPaper.PathHeatWienerSourceLimit
public import HexagonPaper.PathHeatMomentContinuity

@[expose] public section

/-! Actual normalizers, normalized expectations and centered signed
responses on the common Wiener reference. All continuity and moving mesh
limits are instantiated from the native clocks and genuine source bounds. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped Topology BigOperators unitInterval NNReal BoundedContinuousFunction
namespace HexagonPaper
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {Z E K : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Fintype K] [Nonempty K] [TopologicalSpace K] [DiscreteTopology K]
  [MeasurableSpace K] [BorelSpace K] [MeasurableSingletonClass K]
variable (L : ℕ) (μ : Measure E) [IsGaussian μ]
variable (d : PathHeatContinuousSignedSource (pathHeatWienerSourceSpace (Z:=Z) (E:=E) (K:=K) L) (Fin L×I))
  (c : Z→Fin L→C(I,I)) (T : C(Fin L×I,ℝ)→L[ℝ]C(Fin L×I,ℝ))
  (A : C(Fin L×I,C(Fin L×I,ℝ))→L[ℝ]C(Fin L×I,C(Fin L×I,ℝ)))
  (D : Z→C(Fin L×I,C(Fin L×I,ℝ)))

def pathHeatWienerSourceNormalizer (z : Z) : ℝ :=
  pathHeatNormalizer (pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ)
    (fun ω=>d.weight (pathHeatWienerSourceState L c T z ω))

def pathHeatWienerSourceExpectation (z : Z) : ℝ :=
  pathHeatExpectation (pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ)
    (fun ω=>d.weight (pathHeatWienerSourceState L c T z ω))
    (fun ω=>d.phi (pathHeatWienerSourceState L c T z ω))

def pathHeatWienerSourceResponse (z : Z) : ℝ :=
  pathHeatResponse (pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ)
    (fun ω=>d.weight (pathHeatWienerSourceState L c T z ω))
    (fun ω=>d.phi (pathHeatWienerSourceState L c T z ω))
    (fun ω=>d.densityGenerator (pathHeatWienerSourceKernel L A D z) (pathHeatWienerSourceState L c T z ω))
    (fun ω=>d.observableGenerator (pathHeatWienerSourceKernel L A D z) (pathHeatWienerSourceState L c T z ω))

def pathHeatWienerSourceLogNormalizerResponse (z : Z) : ℝ :=
  pathHeatExpectation (pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ)
    (fun ω=>d.weight (pathHeatWienerSourceState L c T z ω))
    (fun ω=>d.densityGenerator (pathHeatWienerSourceKernel L A D z) (pathHeatWienerSourceState L c T z ω))

def pathHeatWienerSourceApproximateNormalizer (n : ℕ) (z : Z) : ℝ :=
  pathHeatNormalizer (pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ)
    (fun ω=>d.weight (pathHeatWienerSourceApproximateState L c T n z ω))

def pathHeatWienerSourceApproximateExpectation (n : ℕ) (z : Z) : ℝ :=
  pathHeatExpectation (pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ)
    (fun ω=>d.weight (pathHeatWienerSourceApproximateState L c T n z ω))
    (fun ω=>d.phi (pathHeatWienerSourceApproximateState L c T n z ω))

def pathHeatWienerSourceApproximateResponse (n : ℕ) (z : Z) : ℝ :=
  pathHeatResponse (pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ)
    (fun ω=>d.weight (pathHeatWienerSourceApproximateState L c T n z ω))
    (fun ω=>d.phi (pathHeatWienerSourceApproximateState L c T n z ω))
    (fun ω=>d.densityGenerator (pathHeatWienerSourceApproximateKernel L A D n z) (pathHeatWienerSourceApproximateState L c T n z ω))
    (fun ω=>d.observableGenerator (pathHeatWienerSourceApproximateKernel L A D n z) (pathHeatWienerSourceApproximateState L c T n z ω))

theorem pathHeatWienerSource_positive_normalizer (κA κ C : ℝ≥0)
    (hA : ∀K,‖A K‖≤κA*‖K‖)
    (hD : ∀z,‖D z‖≤κ)
    (hgrowth : ∀z a k p,|d.ell (z,((a,k),p))|≤C*(1+‖a‖+‖p‖)) (z : Z) :
    0<pathHeatWienerSourceNormalizer L μ d c T z :=
  pathHeat_normalizer_positive (pathHeatWienerSource_dominatedData L μ d c T A D κA κ C hA hD hgrowth z)

theorem pathHeatWienerSource_moving_normalized_limits (κA κ C : ℝ≥0)
    (hA : ∀K,‖A K‖≤κA*‖K‖)
    (hDc : Continuous D) (hD : ∀z,‖D z‖≤κ) (hc : ∀l,Continuous (fun z=>c z l))
    (hgrowth : ∀z a k p,|d.ell (z,((a,k),p))|≤C*(1+‖a‖+‖p‖))
    (z : ℕ→Z) (z₀ : Z) (hz : Tendsto z atTop (𝓝 z₀)) :
    (0<pathHeatWienerSourceNormalizer L μ d c T z₀) ∧
    Tendsto (fun n=>pathHeatWienerSourceApproximateNormalizer L μ d c T n (z n)) atTop
      (𝓝 (pathHeatWienerSourceNormalizer L μ d c T z₀)) ∧
    Tendsto (fun n=>pathHeatWienerSourceApproximateExpectation L μ d c T n (z n)) atTop
      (𝓝 (pathHeatWienerSourceExpectation L μ d c T z₀)) ∧
    Tendsto (fun n=>pathHeatWienerSourceApproximateResponse L μ d c T A D n (z n)) atTop
      (𝓝 (pathHeatWienerSourceResponse L μ d c T A D z₀)) := by
  have hv := fun ω=>pathHeatWienerSource_moving_values L d c T A D hc hDc z z₀ hz ω
  exact pathHeat_normalized_limits
    (fun n=>pathHeatWienerSource_approximate_dominatedData L μ d c T A D κA κ C hA hD hgrowth n (z n))
    (pathHeatWienerSource_dominatedData L μ d c T A D κA κ C hA hD hgrowth z₀)
    (.of_forall (fun ω=>(hv ω).1)) (.of_forall (fun ω=>(hv ω).2.1))
    (.of_forall (fun ω=>(hv ω).2.2.1)) (.of_forall (fun ω=>(hv ω).2.2.2))

theorem continuous_pathHeatWienerSourceState_parameter
    (hc : ∀l,Continuous (fun z=>c z l)) (ω : pathHeatGeneralBaseSample E (Fin L) K) :
    Continuous (fun z=>pathHeatWienerSourceState L c T z ω) := by
  have hp := T.continuous.comp
    (continuous_pathHeatFlatClockPath_family L c (fun _=>ω.1.2) hc (fun _=>continuous_const))
  exact continuous_id.prodMk (continuous_const.prodMk hp)

theorem continuous_pathHeatWienerSourceKernel (hD : Continuous D) :
    Continuous (pathHeatWienerSourceKernel L A D) :=
  (pathHeatTreeKernelBCF L).continuous.comp (A.continuous.comp hD)

theorem pathHeatWienerSource_continuous_moments [Nonempty Z] (κA κ C : ℝ≥0)
    (hA : ∀K,‖A K‖≤κA*‖K‖)
    (hDc : Continuous D) (hD : ∀z,‖D z‖≤κ) (hc : ∀l,Continuous (fun z=>c z l))
    (hgrowth : ∀z a k p,|d.ell (z,((a,k),p))|≤C*(1+‖a‖+‖p‖)) :
    Continuous (pathHeatWienerSourceNormalizer L μ d c T) ∧
    Continuous (pathHeatWienerSourceExpectation L μ d c T) ∧
    Continuous (pathHeatWienerSourceResponse L μ d c T A D) := by
  have hstate (ω : pathHeatGeneralBaseSample E (Fin L) K) :
      Continuous (fun z=>pathHeatWienerSourceState L c T z ω) :=
    continuous_pathHeatWienerSourceState_parameter L c T hc ω
  have hkernel := continuous_pathHeatWienerSourceKernel L A D hDc
  have hH (ω : pathHeatGeneralBaseSample E (Fin L) K) : Continuous (fun z=>
      d.densityGenerator (pathHeatWienerSourceKernel L A D z) (pathHeatWienerSourceState L c T z ω)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact d.tendsto_densityGenerator _ _ _ _ (hstate ω).continuousAt.tendsto hkernel.continuousAt.tendsto
  have hJ (ω : pathHeatGeneralBaseSample E (Fin L) K) : Continuous (fun z=>
      d.observableGenerator (pathHeatWienerSourceKernel L A D z) (pathHeatWienerSourceState L c T z ω)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact d.tendsto_observableGenerator _ _ _ _ (hstate ω).continuousAt.tendsto hkernel.continuousAt.tendsto
  exact continuous_pathHeat_normalized_moments _ _ _ _ _ _ _ _
    (fun z=>pathHeatWienerSource_dominatedData L μ d c T A D κA κ C hA hD hgrowth z)
    (.of_forall (fun ω=>d.continuous_weight.comp (hstate ω)))
    (.of_forall (fun ω=>d.continuous_phi.comp (hstate ω)))
    (.of_forall hH) (.of_forall hJ)

theorem pathHeatWienerSource_continuous_log_normalizer_response [Nonempty Z] (κA κ C : ℝ≥0)
    (hA : ∀K,‖A K‖≤κA*‖K‖)
    (hDc : Continuous D) (hD : ∀z,‖D z‖≤κ) (hc : ∀l,Continuous (fun z=>c z l))
    (hgrowth : ∀z a k p,|d.ell (z,((a,k),p))|≤C*(1+‖a‖+‖p‖)) :
    Continuous (pathHeatWienerSourceLogNormalizerResponse L μ d c T A D) := by
  have hstate (ω : pathHeatGeneralBaseSample E (Fin L) K) :
      Continuous (fun z=>pathHeatWienerSourceState L c T z ω) :=
    continuous_pathHeatWienerSourceState_parameter L c T hc ω
  have hkernel := continuous_pathHeatWienerSourceKernel L A D hDc
  have hH (ω : pathHeatGeneralBaseSample E (Fin L) K) : Continuous (fun z=>
      d.densityGenerator (pathHeatWienerSourceKernel L A D z) (pathHeatWienerSourceState L c T z ω)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact d.tendsto_densityGenerator _ _ _ _ (hstate ω).continuousAt.tendsto hkernel.continuousAt.tendsto
  exact continuous_pathHeat_density_expectation _ _ _ _ _ _ _ _
    (fun z=>pathHeatWienerSource_dominatedData L μ d c T A D κA κ C hA hD hgrowth z)
    (.of_forall (fun ω=>d.continuous_weight.comp (hstate ω))) (.of_forall hH)

end HexagonPaper
