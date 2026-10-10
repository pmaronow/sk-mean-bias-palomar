module
public import HexagonPaper.PathHeatSectionwiseSource
public import HexagonPaper.PathHeatWienerSourceLimit
public import HexagonPaper.PathHeatClockKernel

@[expose] public section

/-! Actual uniform-count common-Wiener moments for the source with only
fixed-auxiliary total-variation continuity. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped Topology BigOperators unitInterval NNReal BoundedContinuousFunction
namespace HexagonPaper
variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Fintype K] [Nonempty K] [TopologicalSpace K] [DiscreteTopology K]
  [MeasurableSpace K] [BorelSpace K] [MeasurableSingletonClass K]
variable {L : ℕ} {a b : ℝ}
variable (μ : Measure E)
  (d : PathHeatSectionwiseSignedSource (Icc a b) E K (Fin L×I))
  (c : Icc a b→Fin L→C(I,I)) (dc : Icc a b→Fin L→C(I,ℝ))
  (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)

def pathHeatSectionwiseWienerNormalizer (z : Icc a b) : ℝ :=
  pathHeatNormalizer (pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ)
    (fun ω=>d.weight (pathHeatWienerSourceState L c (pathHeatTreeMixedOperator δ W) z ω))

def pathHeatSectionwiseWienerExpectation (z : Icc a b) : ℝ :=
  pathHeatExpectation (pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ)
    (fun ω=>d.weight (pathHeatWienerSourceState L c (pathHeatTreeMixedOperator δ W) z ω))
    (fun ω=>d.phi (pathHeatWienerSourceState L c (pathHeatTreeMixedOperator δ W) z ω))

def pathHeatSectionwiseWienerResponse (z : Icc a b) : ℝ :=
  pathHeatResponse (pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ)
    (fun ω=>d.weight (pathHeatWienerSourceState L c (pathHeatTreeMixedOperator δ W) z ω))
    (fun ω=>d.phi (pathHeatWienerSourceState L c (pathHeatTreeMixedOperator δ W) z ω))
    (fun ω=>d.densityGenerator (pathHeatWienerSourceKernel L (pathHeatTreeMixedKernelOperator δ W)
      (fun z=>pathHeatClockRawKernel (dc z)) z) (pathHeatWienerSourceState L c (pathHeatTreeMixedOperator δ W) z ω))
    (fun ω=>d.observableGenerator (pathHeatWienerSourceKernel L (pathHeatTreeMixedKernelOperator δ W)
      (fun z=>pathHeatClockRawKernel (dc z)) z) (pathHeatWienerSourceState L c (pathHeatTreeMixedOperator δ W) z ω))

def pathHeatSectionwiseWienerLogNormalizerResponse (z : Icc a b) : ℝ :=
  pathHeatExpectation (pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ)
    (fun ω=>d.weight (pathHeatWienerSourceState L c (pathHeatTreeMixedOperator δ W) z ω))
    (fun ω=>d.densityGenerator (pathHeatWienerSourceKernel L (pathHeatTreeMixedKernelOperator δ W)
      (fun z=>pathHeatClockRawKernel (dc z)) z) (pathHeatWienerSourceState L c (pathHeatTreeMixedOperator δ W) z ω))

end HexagonPaper
