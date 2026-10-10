module
public import HexagonPaper.PathHeatSectionwiseWienerData
public import HexagonPaper.PathHeatSectionwiseMoments
public import HexagonPaper.PathHeatWienerSourceMoments

@[expose] public section

/-! Genuine moving path and covariance limits for the literal sectionwise
source. All Gaussian auxiliaries are held fixed in each pointwise limit;
actual common reference domination is derived from weakly measurable jets. -/
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
local instance instSectionwiseWienerLimitPathMeasurable : MeasurableSpace C(Fin L×I,ℝ) := borel _
local instance instSectionwiseWienerLimitPathBorel : BorelSpace C(Fin L×I,ℝ) := ⟨rfl⟩

 theorem pathHeatSectionwiseWiener_actual_dominatedData
    (μ : Measure E) [IsGaussian μ] (hab : a≤b)
    (d : PathHeatSectionwiseSignedSource (Icc a b) E K (Fin L×I))
    (C : ℝ≥0) (hs : PathHeatSectionwiseAnalyticSource a b hab d C)
    (c : Icc a b→Fin L→C(I,I)) (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (D : Icc a b→C(Fin L×I,C(Fin L×I,ℝ))) (κ : ℝ≥0) (hD : ∀z,‖D z‖≤κ) (z : Icc a b) :
    PathHeatDominatedData (pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ)
      (fun ω=>d.weight (pathHeatWienerSourceState L c (pathHeatTreeMixedOperator δ W) z ω))
      (fun ω=>d.phi (pathHeatWienerSourceState L c (pathHeatTreeMixedOperator δ W) z ω))
      (fun ω=>d.densityGenerator (pathHeatWienerSourceKernel L (pathHeatTreeMixedKernelOperator δ W) D z)
        (pathHeatWienerSourceState L c (pathHeatTreeMixedOperator δ W) z ω))
      (fun ω=>d.observableGenerator (pathHeatWienerSourceKernel L (pathHeatTreeMixedKernelOperator δ W) D z)
        (pathHeatWienerSourceState L c (pathHeatTreeMixedOperator δ W) z ω))
      (pathHeatGeneralEnvelope (C*(1+‖pathHeatTreeMixedOperator (E:=ℝ) δ W‖))) d.B
      (d.densityBound (pathHeatWienerMixedKernelBound δ W*κ))
      (d.observableBound (pathHeatWienerMixedKernelBound δ W*κ)) := by
  let T : C(Fin L×I,ℝ)→L[ℝ]C(Fin L×I,ℝ) := pathHeatTreeMixedOperator δ W
  apply pathHeatSectionwiseWiener_dominatedData μ hab d C hs δ W (D z) κ (hD z) ‖T‖ (norm_nonneg T)
    (fun ω=>T (pathHeatFlatClockPath L (c z) ω.1.2))
  · exact ((continuous_snd.snd).comp (continuous_pathHeatWienerSourceState (E:=E) (K:=K) L c T z)).measurable
  · intro ω
    exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_pathHeatFlatClockPath_le L _ _) (norm_nonneg T))

 theorem pathHeatSectionwiseWiener_approximate_dominatedData
    (μ : Measure E) [IsGaussian μ] (hab : a≤b)
    (d : PathHeatSectionwiseSignedSource (Icc a b) E K (Fin L×I))
    (C : ℝ≥0) (hs : PathHeatSectionwiseAnalyticSource a b hab d C)
    (c : Icc a b→Fin L→C(I,I)) (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (D : Icc a b→C(Fin L×I,C(Fin L×I,ℝ))) (κ : ℝ≥0) (hD : ∀z,‖D z‖≤κ)
    (n : ℕ) (z : Icc a b) :
    PathHeatDominatedData (pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ)
      (fun ω=>d.weight (pathHeatWienerSourceApproximateState L c (pathHeatTreeMixedOperator δ W) n z ω))
      (fun ω=>d.phi (pathHeatWienerSourceApproximateState L c (pathHeatTreeMixedOperator δ W) n z ω))
      (fun ω=>d.densityGenerator (pathHeatWienerSourceApproximateKernel L (pathHeatTreeMixedKernelOperator δ W) D n z)
        (pathHeatWienerSourceApproximateState L c (pathHeatTreeMixedOperator δ W) n z ω))
      (fun ω=>d.observableGenerator (pathHeatWienerSourceApproximateKernel L (pathHeatTreeMixedKernelOperator δ W) D n z)
        (pathHeatWienerSourceApproximateState L c (pathHeatTreeMixedOperator δ W) n z ω))
      (pathHeatGeneralEnvelope (C*(1+‖pathHeatTreeMixedOperator (E:=ℝ) δ W‖))) d.B
      (d.densityBound (pathHeatWienerMixedKernelBound δ W*κ))
      (d.observableBound (pathHeatWienerMixedKernelBound δ W*κ)) := by
  let T : C(Fin L×I,ℝ)→L[ℝ]C(Fin L×I,ℝ) := pathHeatTreeMixedOperator δ W
  apply pathHeatSectionwiseWiener_dominatedData μ hab d C hs δ W (pathHeatTreeKernelSample n L (D z))
    κ ((norm_pathHeatTreeKernelSample_le n L _).trans (hD z)) ‖T‖ (norm_nonneg T)
    (fun ω=>T (pathHeatTreeBernsteinOperator n L (pathHeatFlatClockPath L (c z) ω.1.2)))
  · exact ((continuous_snd.snd).comp
      (continuous_pathHeatWienerSourceApproximateState (E:=E) (K:=K) L c T n z)).measurable
  · intro ω
    exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      ((norm_pathHeatTreeBernsteinSample_le n L _).trans (norm_pathHeatFlatClockPath_le L _ _)) (norm_nonneg T))

 theorem pathHeatSectionwiseWiener_moving_values
    (d : PathHeatSectionwiseSignedSource (Icc a b) E K (Fin L×I))
    (c : Icc a b→Fin L→C(I,I)) (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (D : Icc a b→C(Fin L×I,C(Fin L×I,ℝ)))
    (hc : ∀l,Continuous (fun z=>c z l)) (hD : Continuous D)
    (z : ℕ→Icc a b) (z₀ : Icc a b) (hz : Tendsto z atTop (𝓝 z₀))
    (ω : pathHeatGeneralBaseSample E (Fin L) K) :
    Tendsto (fun n=>d.weight (pathHeatWienerSourceApproximateState L c (pathHeatTreeMixedOperator δ W) n (z n) ω)) atTop
      (𝓝 (d.weight (pathHeatWienerSourceState L c (pathHeatTreeMixedOperator δ W) z₀ ω))) ∧
    Tendsto (fun n=>d.phi (pathHeatWienerSourceApproximateState L c (pathHeatTreeMixedOperator δ W) n (z n) ω)) atTop
      (𝓝 (d.phi (pathHeatWienerSourceState L c (pathHeatTreeMixedOperator δ W) z₀ ω))) ∧
    Tendsto (fun n=>d.densityGenerator (pathHeatWienerSourceApproximateKernel L (pathHeatTreeMixedKernelOperator δ W) D n (z n))
      (pathHeatWienerSourceApproximateState L c (pathHeatTreeMixedOperator δ W) n (z n) ω)) atTop
      (𝓝 (d.densityGenerator (pathHeatWienerSourceKernel L (pathHeatTreeMixedKernelOperator δ W) D z₀)
        (pathHeatWienerSourceState L c (pathHeatTreeMixedOperator δ W) z₀ ω))) ∧
    Tendsto (fun n=>d.observableGenerator (pathHeatWienerSourceApproximateKernel L (pathHeatTreeMixedKernelOperator δ W) D n (z n))
      (pathHeatWienerSourceApproximateState L c (pathHeatTreeMixedOperator δ W) n (z n) ω)) atTop
      (𝓝 (d.observableGenerator (pathHeatWienerSourceKernel L (pathHeatTreeMixedKernelOperator δ W) D z₀)
        (pathHeatWienerSourceState L c (pathHeatTreeMixedOperator δ W) z₀ ω))) := by
  let T : C(Fin L×I,ℝ)→L[ℝ]C(Fin L×I,ℝ) := pathHeatTreeMixedOperator δ W
  let A : C(Fin L×I,C(Fin L×I,ℝ))→L[ℝ]C(Fin L×I,C(Fin L×I,ℝ)) := pathHeatTreeMixedKernelOperator δ W
  have hp := T.continuous.continuousAt.tendsto.comp
    (tendsto_pathHeatFlatClockPath_Bernstein_moving L (fun n=>c (z n)) (c z₀) ω.1.2
      (fun l=>(hc l).continuousAt.tendsto.comp hz))
  exact (d.section (ω.1.1,ω.2)).moving_values _ _ _ _ (hz.prodMk_nhds hp)
    (tendsto_pathHeatWienerSourceApproximateKernel L A D hD z z₀ hz)

theorem pathHeatSectionwiseWiener_moving_values_succ
    (d : PathHeatSectionwiseSignedSource (Icc a b) E K (Fin L×I))
    (c : Icc a b→Fin L→C(I,I)) (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (D : Icc a b→C(Fin L×I,C(Fin L×I,ℝ)))
    (hc : ∀l,Continuous (fun z=>c z l)) (hD : Continuous D)
    (z : ℕ→Icc a b) (z₀ : Icc a b) (hz : Tendsto z atTop (𝓝 z₀))
    (ω : pathHeatGeneralBaseSample E (Fin L) K) :
    Tendsto (fun n=>d.weight (pathHeatWienerSourceApproximateState L c (pathHeatTreeMixedOperator δ W) (n+1) (z n) ω)) atTop
      (𝓝 (d.weight (pathHeatWienerSourceState L c (pathHeatTreeMixedOperator δ W) z₀ ω))) ∧
    Tendsto (fun n=>d.phi (pathHeatWienerSourceApproximateState L c (pathHeatTreeMixedOperator δ W) (n+1) (z n) ω)) atTop
      (𝓝 (d.phi (pathHeatWienerSourceState L c (pathHeatTreeMixedOperator δ W) z₀ ω))) ∧
    Tendsto (fun n=>d.densityGenerator (pathHeatWienerSourceApproximateKernel L (pathHeatTreeMixedKernelOperator δ W) D (n+1) (z n))
      (pathHeatWienerSourceApproximateState L c (pathHeatTreeMixedOperator δ W) (n+1) (z n) ω)) atTop
      (𝓝 (d.densityGenerator (pathHeatWienerSourceKernel L (pathHeatTreeMixedKernelOperator δ W) D z₀) (pathHeatWienerSourceState L c (pathHeatTreeMixedOperator δ W) z₀ ω))) ∧
    Tendsto (fun n=>d.observableGenerator (pathHeatWienerSourceApproximateKernel L (pathHeatTreeMixedKernelOperator δ W) D (n+1) (z n))
      (pathHeatWienerSourceApproximateState L c (pathHeatTreeMixedOperator δ W) (n+1) (z n) ω)) atTop
      (𝓝 (d.observableGenerator (pathHeatWienerSourceKernel L (pathHeatTreeMixedKernelOperator δ W) D z₀) (pathHeatWienerSourceState L c (pathHeatTreeMixedOperator δ W) z₀ ω))) := by
  have hv := pathHeatSectionwiseWiener_moving_values d c δ W D hc hD
    (fun n=>z (n-1)) z₀ (hz.comp (tendsto_sub_atTop_nat 1)) ω
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [Function.comp_def,Nat.add_sub_cancel] using hv.1.comp (tendsto_add_atTop_nat 1)
  · simpa only [Function.comp_def,Nat.add_sub_cancel] using hv.2.1.comp (tendsto_add_atTop_nat 1)
  · simpa only [Function.comp_def,Nat.add_sub_cancel] using hv.2.2.1.comp (tendsto_add_atTop_nat 1)
  · simpa only [Function.comp_def,Nat.add_sub_cancel] using hv.2.2.2.comp (tendsto_add_atTop_nat 1)

end HexagonPaper
