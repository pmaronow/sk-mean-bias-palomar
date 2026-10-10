module
public import HexagonPaper.PathHeatWienerFiniteReordered
public import HexagonPaper.PathHeatWienerSourceMoments
public import HexagonPaper.PathHeatRawDerivativeLimit
public import HexagonPaper.PathHeatClockKernelFamily

@[expose] public section

/-! Complete differentiation on the actual common Wiener reference.
The finite derivatives are constructed from source signed jets, actual
Brownian observation laws and untouched auxiliary integration. The limit
uses the proved Bernstein path/kernel convergence and common Fernique
bound, so no finite or limiting response formula is a hypothesis here. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped Topology BigOperators unitInterval NNReal BoundedContinuousFunction
namespace HexagonPaper
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Fintype K] [Nonempty K] [TopologicalSpace K] [DiscreteTopology K]
  [MeasurableSpace K] [BorelSpace K] [MeasurableSingletonClass K]
variable {L : ℕ} {a b : ℝ}

def pathHeatWienerMixedKernelBound (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ) : ℝ≥0 :=
  ⟨(pathHeatTreeMixedBound δ W)^2,sq_nonneg _⟩

theorem pathHeatWiener_mixed_differentiation
    (μ : Measure E) [IsGaussian μ] (hab : a≤b)
    (d : PathHeatContinuousSignedSource (Icc a b×((E×K)×C(Fin L×I,ℝ))) (Fin L×I))
    (C : ℝ≥0) (hsource : PathHeatWienerAnalyticSource a b hab d C)
    (c : Icc a b→Fin L→C(I,I)) (dc : Icc a b→Fin L→C(I,ℝ))
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (hc : ∀l,Continuous (fun z=>c z l))
    (hdcc : ∀l,Continuous (fun z=>dc z l))
    (hstrict : ∀z : Icc a b,z.val∈Ioo a b→∀l,StrictMono (c z l))
    (hroot : ∀z l,c z l 0=0)
    (hdc : ∀z∈Ioo a b,∀l t,
      HasDerivAt (fun u=>(c (projIcc a b hab u) l t:ℝ))
        (dc (projIcc a b hab z) l t) z)
    (κ : ℝ≥0) (hD : ∀z,‖pathHeatClockRawKernel (dc z)‖≤κ)
    (x : ℝ) (hx : x∈Ioo a b) :
    (0<pathHeatWienerSourceNormalizer L μ d c (pathHeatTreeMixedOperator δ W) (projIcc a b hab x)) ∧
    HasDerivAt
      (fun u=>pathHeatWienerSourceExpectation L μ d c (pathHeatTreeMixedOperator δ W) (projIcc a b hab u))
      (pathHeatWienerSourceResponse L μ d c (pathHeatTreeMixedOperator δ W)
        (pathHeatTreeMixedKernelOperator δ W) (fun z=>pathHeatClockRawKernel (dc z))
        (projIcc a b hab x)) x ∧
    HasDerivAt
      (fun u=>Real.log (pathHeatWienerSourceNormalizer L μ d c (pathHeatTreeMixedOperator δ W) (projIcc a b hab u)))
      (pathHeatWienerSourceLogNormalizerResponse L μ d c (pathHeatTreeMixedOperator δ W)
        (pathHeatTreeMixedKernelOperator δ W) (fun z=>pathHeatClockRawKernel (dc z))
        (projIcc a b hab x)) x := by
  let T : C(Fin L×I,ℝ)→L[ℝ]C(Fin L×I,ℝ) := pathHeatTreeMixedOperator δ W
  let A : C(Fin L×I,C(Fin L×I,ℝ))→L[ℝ]C(Fin L×I,C(Fin L×I,ℝ)) := pathHeatTreeMixedKernelOperator δ W
  let D := fun z=>pathHeatClockRawKernel (dc z)
  let ν := pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ
  let state := fun u=>pathHeatWienerSourceState (E:=E) (K:=K) L c T (projIcc a b hab u)
  let stateN := fun n u=>pathHeatWienerSourceApproximateState (E:=E) (K:=K) L c T (n+1) (projIcc a b hab u)
  let kernel := fun u=>pathHeatWienerSourceKernel L A D (projIcc a b hab u)
  let kernelN := fun n u=>pathHeatWienerSourceApproximateKernel L A D (n+1) (projIcc a b hab u)
  let weight := fun u ω=>d.weight (state u ω)
  let phi := fun u ω=>d.phi (state u ω)
  let H := fun u ω=>d.densityGenerator (kernel u) (state u ω)
  let J := fun u ω=>d.observableGenerator (kernel u) (state u ω)
  let weightN := fun n u ω=>d.weight (stateN n u ω)
  let phiN := fun n u ω=>d.phi (stateN n u ω)
  let HN := fun n u ω=>d.densityGenerator (kernelN n u) (stateN n u ω)
  let JN := fun n u ω=>d.observableGenerator (kernelN n u) (stateN n u ω)
  let κA := pathHeatWienerMixedKernelBound δ W
  have hA : ∀k,‖A k‖≤κA*‖k‖ := fun k=>norm_pathHeatTreeMixedKernelOperator_apply_le δ W k
  have hDc : Continuous D := continuous_pathHeatRawClockKernel_family dc hdcc
  have hg : ∀z aux k p,|d.ell (z,((aux,k),p))|≤C*(1+‖aux‖+‖p‖) :=
    fun z aux k p=>hsource.ell_growth z (aux,k) p
  have dataN (n : ℕ) (u : ℝ) : PathHeatDominatedData ν (weightN n u) (phiN n u) (HN n u) (JN n u)
      (pathHeatGeneralEnvelope (C*(1+‖T‖))) d.B (d.densityBound (κA*κ)) (d.observableBound (κA*κ)) :=
    pathHeatWienerSource_approximate_dominatedData L μ d c T A D κA κ C hA hD hg (n+1) (projIcc a b hab u)
  have data (u : ℝ) : PathHeatDominatedData ν (weight u) (phi u) (H u) (J u)
      (pathHeatGeneralEnvelope (C*(1+‖T‖))) d.B (d.densityBound (κA*κ)) (d.observableBound (κA*κ)) :=
    pathHeatWienerSource_dominatedData L μ d c T A D κA κ C hA hD hg (projIcc a b hab u)
  have limits (z : ℕ→ℝ) (y : ℝ) (hz : Tendsto z atTop (𝓝 y)) :
      (∀ᵐω ∂ν,Tendsto (fun n=>weightN n (z n) ω) atTop (𝓝 (weight y ω))) ∧
      (∀ᵐω ∂ν,Tendsto (fun n=>phiN n (z n) ω) atTop (𝓝 (phi y ω))) ∧
      (∀ᵐω ∂ν,Tendsto (fun n=>HN n (z n) ω) atTop (𝓝 (H y ω))) ∧
      (∀ᵐω ∂ν,Tendsto (fun n=>JN n (z n) ω) atTop (𝓝 (J y ω))) := by
    have hp : Tendsto (fun n=>projIcc a b hab (z n)) atTop (𝓝 (projIcc a b hab y)) :=
      continuous_projIcc.continuousAt.tendsto.comp hz
    have hl := fun ω=>pathHeatWienerSource_moving_values_succ L d c T A D hc hDc
      (fun n=>projIcc a b hab (z n)) (projIcc a b hab y) hp ω
    exact ⟨.of_forall (fun ω=>(hl ω).1),.of_forall (fun ω=>(hl ω).2.1),
      .of_forall (fun ω=>(hl ω).2.2.1),.of_forall (fun ω=>(hl ω).2.2.2)⟩
  have finiteZ (n : ℕ) (u : ℝ) (hu : u∈Ioo a b) :
      HasDerivAt (fun v=>pathHeatNormalizer ν (weightN n v)) (∫ω,weightN n u ω*HN n u ω∂ν) u := by
    exact (pathHeatWiener_finite_reordered_raw_derivatives μ hab d C hsource c dc δ W
      (show n+1≠0 by omega) hstrict hroot hdc hdcc κ hD u hu).1
  have finiteN (n : ℕ) (u : ℝ) (hu : u∈Ioo a b) :
      HasDerivAt (fun v=>∫ω,weightN n v ω*phiN n v ω∂ν)
        (∫ω,weightN n u ω*(JN n u ω+phiN n u ω*HN n u ω)∂ν) u := by
    exact (pathHeatWiener_finite_reordered_raw_derivatives μ hab d C hsource c dc δ W
      (show n+1≠0 by omega) hstrict hroot hdc hdcc κ hD u hu).2
  exact hasDerivAt_pathHeat_expectation_log_normalizer_limits weightN phiN HN JN weight phi H J
    (pathHeatGeneralEnvelope (C*(1+‖T‖))) d.B (d.densityBound (κA*κ)) (d.observableBound (κA*κ))
    a b x hx dataN data limits finiteZ finiteN

end HexagonPaper
