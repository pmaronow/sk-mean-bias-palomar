module
public import HexagonPaper.PathHeatSectionwiseNativeWienerModel

@[expose] public section

/-! The original-index counting moments are exactly the internally extended
flat-Wiener moments; normalizers retain the finite counting mass. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped Topology BigOperators unitInterval NNReal ENNReal BoundedContinuousFunction
namespace HexagonPaper
set_option maxHeartbeats 1800000
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
variable (μ : Measure E) [IsGaussian μ]
  (d : PathHeatSectionwiseSignedSource (Icc a b) E K X)
  (ι : C(X,Fin L×I)) (c : Icc a b→Fin L→C(I,I)) (dc : Icc a b→Fin L→C(I,ℝ))
  (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ) (z : Icc a b)

theorem pathHeatSectionwiseNativeWienerNormalizer_eq_card_flat :
    pathHeatSectionwiseNativeWienerNormalizer μ d ι c δ W z=(Fintype.card K:ℝ)*
      pathHeatSectionwiseWienerNormalizer μ (pathHeatSectionwiseNativeSourceExtension ι d) c δ W z := by
  unfold pathHeatSectionwiseNativeWienerNormalizer
  rw [pathHeatGeneralCountMeasure_eq_card_smul_uniform,pathHeatNormalizer_nat_smul]
  rfl

theorem pathHeatSectionwiseNativeWienerExpectation_eq_flat :
    pathHeatSectionwiseNativeWienerExpectation μ d ι c δ W z=
      pathHeatSectionwiseWienerExpectation μ (pathHeatSectionwiseNativeSourceExtension ι d) c δ W z := by
  unfold pathHeatSectionwiseNativeWienerExpectation
  rw [pathHeatGeneralCountMeasure_eq_card_smul_uniform,pathHeatExpectation_nat_smul _ _ _ _ Fintype.card_ne_zero]
  rfl

theorem pathHeatSectionwiseNativeWienerResponse_eq_flat :
    pathHeatSectionwiseNativeWienerResponse μ d ι c dc δ W z=
      pathHeatSectionwiseWienerResponse μ (pathHeatSectionwiseNativeSourceExtension ι d) c dc δ W z := by
  unfold pathHeatSectionwiseNativeWienerResponse
  rw [pathHeatGeneralCountMeasure_eq_card_smul_uniform,pathHeatResponse_nat_smul _ _ _ _ _ _ Fintype.card_ne_zero]
  have hH (ω : pathHeatGeneralBaseSample E (Fin L) K) :
      (pathHeatSectionwiseNativeSourceExtension ι d).densityGenerator
        (pathHeatWienerSourceKernel L (pathHeatTreeMixedKernelOperator δ W)
          (fun z=>pathHeatClockRawKernel (dc z)) z)
        (pathHeatWienerSourceState L c (pathHeatTreeMixedOperator δ W) z ω)=
      d.densityGenerator (pathHeatSectionwiseNativeWienerKernel ι dc δ W z)
        (pathHeatSectionwiseNativeWienerState ι c δ W z ω) :=
    pathHeatSectionwiseNativeSourceExtension_densityGenerator_continuousKernel ι d _ _
  have hJ (ω : pathHeatGeneralBaseSample E (Fin L) K) :
      (pathHeatSectionwiseNativeSourceExtension ι d).observableGenerator
        (pathHeatWienerSourceKernel L (pathHeatTreeMixedKernelOperator δ W)
          (fun z=>pathHeatClockRawKernel (dc z)) z)
        (pathHeatWienerSourceState L c (pathHeatTreeMixedOperator δ W) z ω)=
      d.observableGenerator (pathHeatSectionwiseNativeWienerKernel ι dc δ W z)
        (pathHeatSectionwiseNativeWienerState ι c δ W z ω) :=
    pathHeatSectionwiseNativeSourceExtension_observableGenerator_continuousKernel ι d _ _
  unfold pathHeatSectionwiseWienerResponse
  simp_rw [hH,hJ]
  rfl

theorem pathHeatSectionwiseNativeWienerLogNormalizerResponse_eq_flat :
    pathHeatSectionwiseNativeWienerLogNormalizerResponse μ d ι c dc δ W z=
      pathHeatSectionwiseWienerLogNormalizerResponse μ (pathHeatSectionwiseNativeSourceExtension ι d) c dc δ W z := by
  unfold pathHeatSectionwiseNativeWienerLogNormalizerResponse
  rw [pathHeatGeneralCountMeasure_eq_card_smul_uniform,pathHeatExpectation_nat_smul _ _ _ _ Fintype.card_ne_zero]
  have hH (ω : pathHeatGeneralBaseSample E (Fin L) K) :
      (pathHeatSectionwiseNativeSourceExtension ι d).densityGenerator
        (pathHeatWienerSourceKernel L (pathHeatTreeMixedKernelOperator δ W)
          (fun z=>pathHeatClockRawKernel (dc z)) z)
        (pathHeatWienerSourceState L c (pathHeatTreeMixedOperator δ W) z ω)=
      d.densityGenerator (pathHeatSectionwiseNativeWienerKernel ι dc δ W z)
        (pathHeatSectionwiseNativeWienerState ι c δ W z ω) :=
    pathHeatSectionwiseNativeSourceExtension_densityGenerator_continuousKernel ι d _ _
  unfold pathHeatSectionwiseWienerLogNormalizerResponse
  simp_rw [hH]
  rfl

end HexagonPaper
