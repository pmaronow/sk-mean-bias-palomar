module
public import HexagonPaper.PathHeatNativeGeneratorTransfer
public import HexagonPaper.PathHeatWienerEndpoints
public import HexagonPaper.PathHeatClockCompactBound
public import HexagonPaper.PathHeatCountingNormalization
public import HexagonPaper.PathHeatPrintedResponse

@[expose] public section

/-! Source-level Gaussian heat differentiation on the original compact
finite-coordinate/tree index. The field is the actual fixed tree/terminal
reconstruction of independent clocked canonical Wiener rows. Auxiliary
Gaussian coordinates remain untouched. Counting normalization, signed jets,
normalizer positivity and path derivative limits are constructed internally. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped Topology BigOperators unitInterval NNReal ENNReal BoundedContinuousFunction
namespace HexagonPaper
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X E K : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Fintype K] [Nonempty K] [TopologicalSpace K] [DiscreteTopology K]
  [MeasurableSpace K] [BorelSpace K] [MeasurableSingletonClass K]
variable {L : ℕ} {a b : ℝ}

def pathHeatNativeWienerState (ι : C(X,Fin L×I))
    (c : Icc a b→Fin L→C(I,I)) (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (z : Icc a b) (ω : pathHeatGeneralBaseSample E (Fin L) K) : Icc a b×((E×K)×C(X,ℝ)) :=
  pathHeatNativeSourceRestrictionState ι
    (pathHeatWienerSourceState L c (pathHeatTreeMixedOperator δ W) z ω)

def pathHeatNativeWienerKernel (ι : C(X,Fin L×I))
    (dc : Icc a b→Fin L→C(I,ℝ)) (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (z : Icc a b) : X×X→ᵇℝ :=
  BoundedContinuousFunction.mkOfCompact
    (((pathHeatTreeMixedKernelOperator δ W (pathHeatClockRawKernel (dc z))).uncurry).comp
      (pathHeatIndexPairMap ι))

def pathHeatNativeWienerWeight
    (d : PathHeatContinuousSignedSource (Icc a b×((E×K)×C(X,ℝ))) X)
    (ι : C(X,Fin L×I)) (c : Icc a b→Fin L→C(I,I))
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ) (z : Icc a b)
    (ω : pathHeatGeneralBaseSample E (Fin L) K) : ℝ :=
  d.weight (pathHeatNativeWienerState ι c δ W z ω)

def pathHeatNativeWienerNormalizer
    (μ : Measure E) (d : PathHeatContinuousSignedSource (Icc a b×((E×K)×C(X,ℝ))) X)
    (ι : C(X,Fin L×I)) (c : Icc a b→Fin L→C(I,I))
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ) (z : Icc a b) : ℝ :=
  pathHeatNormalizer (pathHeatGeneralCountMeasure (J:=Fin L) (K:=K) μ)
    (pathHeatNativeWienerWeight d ι c δ W z)

def pathHeatNativeWienerExpectation
    (μ : Measure E) (d : PathHeatContinuousSignedSource (Icc a b×((E×K)×C(X,ℝ))) X)
    (ι : C(X,Fin L×I)) (c : Icc a b→Fin L→C(I,I))
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ) (z : Icc a b) : ℝ :=
  pathHeatExpectation (pathHeatGeneralCountMeasure (J:=Fin L) (K:=K) μ)
    (pathHeatNativeWienerWeight d ι c δ W z)
    (fun ω=>d.phi (pathHeatNativeWienerState ι c δ W z ω))

def pathHeatNativeWienerResponse
    (μ : Measure E) (d : PathHeatContinuousSignedSource (Icc a b×((E×K)×C(X,ℝ))) X)
    (ι : C(X,Fin L×I)) (c : Icc a b→Fin L→C(I,I)) (dc : Icc a b→Fin L→C(I,ℝ))
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ) (z : Icc a b) : ℝ :=
  pathHeatResponse (pathHeatGeneralCountMeasure (J:=Fin L) (K:=K) μ)
    (pathHeatNativeWienerWeight d ι c δ W z)
    (fun ω=>d.phi (pathHeatNativeWienerState ι c δ W z ω))
    (fun ω=>d.densityGenerator (pathHeatNativeWienerKernel ι dc δ W z) (pathHeatNativeWienerState ι c δ W z ω))
    (fun ω=>d.observableGenerator (pathHeatNativeWienerKernel ι dc δ W z) (pathHeatNativeWienerState ι c δ W z ω))

def pathHeatNativeWienerLogNormalizerResponse
    (μ : Measure E) (d : PathHeatContinuousSignedSource (Icc a b×((E×K)×C(X,ℝ))) X)
    (ι : C(X,Fin L×I)) (c : Icc a b→Fin L→C(I,I)) (dc : Icc a b→Fin L→C(I,ℝ))
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ) (z : Icc a b) : ℝ :=
  pathHeatExpectation (pathHeatGeneralCountMeasure (J:=Fin L) (K:=K) μ)
    (pathHeatNativeWienerWeight d ι c δ W z)
    (fun ω=>d.densityGenerator (pathHeatNativeWienerKernel ι dc δ W z) (pathHeatNativeWienerState ι c δ W z ω))


end HexagonPaper
