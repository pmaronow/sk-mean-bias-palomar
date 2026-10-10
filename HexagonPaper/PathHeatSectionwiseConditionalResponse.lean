module
public import HexagonPaper.PathHeatSectionwiseFrozenAuxiliary
public import HexagonPaper.PathHeatWienerFiniteConditionalResponse

@[expose] public section

/-! Actual conditional Wiener/Price response under precisely sectionwise
total-variation continuity. Freezing the true auxiliary coordinates is an
internal construction; the conclusions retain the original weak source. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators unitInterval NNReal BoundedContinuousFunction
namespace HexagonPaper
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Fintype K] [TopologicalSpace K] [DiscreteTopology K]
  [MeasurableSpace K] [BorelSpace K] [MeasurableSingletonClass K]
variable {L n : ℕ} {a b : ℝ}

theorem pathHeatSectionwise_finite_conditional_derivatives
    (hab : a≤b) (d : PathHeatSectionwiseSignedSource (Icc a b) E K (Fin L×I))
    (C : ℝ≥0) (hsource : PathHeatSectionwiseAnalyticSource a b hab d C)
    (c : ℝ→Fin L→C(I,I)) (dc : ℝ→Fin L→C(I,ℝ))
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ) (hn : n≠0)
    (hc : ∀z∈Ioo a b,∀l,StrictMono (c z l))
    (hroot : ∀z l,c z l 0=0)
    (hdc : ∀z∈Ioo a b,∀l t,HasDerivAt (fun u=>(c u l t:ℝ)) (dc z l t) z)
    (hdcc : ∀z∈Ioo a b,∀l,ContinuousAt (fun u=>dc u l) z)
    (aux : E×K) (z : ℝ) (hz : z∈Ioo a b) :
    0<(∫w,d.weight (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W aux z w)
      ∂pathHeatWienerMeshBase (J:=Fin L)) ∧
    HasDerivAt (fun u=>∫w,d.weight
      (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W aux u w)
      ∂pathHeatWienerMeshBase (J:=Fin L))
      (∫w,d.weight (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W aux z w)*
        d.densityGenerator (pathHeatWienerFiniteKernel n L δ W dc z)
          (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W aux z w)
        ∂pathHeatWienerMeshBase (J:=Fin L)) z ∧
    HasDerivAt (fun u=>∫w,d.weight
      (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W aux u w)*
      d.phi (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W aux u w)
      ∂pathHeatWienerMeshBase (J:=Fin L))
      (∫w,d.weight (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W aux z w)*
        (d.observableGenerator (pathHeatWienerFiniteKernel n L δ W dc z)
          (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W aux z w)+
          d.phi (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W aux z w)*
          d.densityGenerator (pathHeatWienerFiniteKernel n L δ W dc z)
            (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W aux z w))
        ∂pathHeatWienerMeshBase (J:=Fin L)) z := by
  have h := pathHeatWiener_finite_conditional_derivatives hab (d.fixedAuxiliary aux)
    (pathHeatWienerAuxGrowthConstant C aux)
    (pathHeatSectionwise_fixedAuxiliary_wiener_analytic hab d C hsource aux)
    c dc δ W hn hc hroot hdc hdcc aux z hz
  dsimp only [pathHeatWienerFiniteConditionalNormalizer,
    pathHeatWienerFiniteConditionalNumerator,
    pathHeatWienerFiniteConditionalNormalizerDerivative,
    pathHeatWienerFiniteConditionalNumeratorDerivative,
    PathHeatContinuousSignedSource.weight,PathHeatContinuousSignedSource.densityGenerator,
    PathHeatContinuousSignedSource.observableGenerator,
    PathHeatSectionwiseSignedSource.weight,PathHeatSectionwiseSignedSource.densityGenerator,
    PathHeatSectionwiseSignedSource.observableGenerator,
    PathHeatSectionwiseSignedSource.fixedAuxiliary,pathHeatWienerFiniteConditionalState] at h ⊢
  exact h

end HexagonPaper
