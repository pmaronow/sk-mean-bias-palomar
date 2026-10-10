module
public import HexagonPaper.PathHeatSectionwiseNativeWienerModel
public import HexagonPaper.PathHeatSectionwiseWienerDifferentiation
public import HexagonPaper.PathHeatClockCompactBound

@[expose] public section

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

theorem pathHeatSectionwiseNativeWiener_differentiation
    (μ : Measure E) [IsGaussian μ] (hab : a≤b)
    (d : PathHeatSectionwiseSignedSource (Icc a b) E K X)
    (C : ℝ≥0) (hsource : PathHeatSectionwiseAnalyticSource a b hab d C)
    (ι : C(X,Fin L×I)) (c : Icc a b→Fin L→C(I,I)) (dc : Icc a b→Fin L→C(I,ℝ))
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (hc : ∀l,Continuous (fun z=>c z l)) (hdcc : ∀l,Continuous (fun z=>dc z l))
    (hstrict : ∀z : Icc a b,z.val∈Ioo a b→∀l,StrictMono (c z l))
    (hroot : ∀z l,c z l 0=0)
    (hdc : ∀z∈Ioo a b,∀l t,
      HasDerivAt (fun u=>(c (projIcc a b hab u) l t:ℝ))
        (dc (projIcc a b hab z) l t) z)
    (x : ℝ) (hx : x∈Ioo a b) :
    (0<pathHeatSectionwiseNativeWienerNormalizer μ d ι c δ W (projIcc a b hab x)) ∧
    HasDerivAt (fun u=>pathHeatSectionwiseNativeWienerExpectation μ d ι c δ W (projIcc a b hab u))
      (pathHeatSectionwiseNativeWienerResponse μ d ι c dc δ W (projIcc a b hab x)) x ∧
    HasDerivAt (fun u=>Real.log (pathHeatSectionwiseNativeWienerNormalizer μ d ι c δ W (projIcc a b hab u)))
      (pathHeatSectionwiseNativeWienerLogNormalizerResponse μ d ι c dc δ W (projIcc a b hab x)) x := by
  let df := pathHeatSectionwiseNativeSourceExtension ι d
  have hs := pathHeatSectionwiseNativeSourceExtension_analytic hab ι d C hsource
  obtain ⟨κ,hκ⟩ := exists_pathHeatClockRawKernel_bound_of_continuous dc hdcc
  have hd := pathHeatSectionwiseWiener_differentiation μ hab df C hs c dc δ W hc hdcc
    hstrict hroot hdc κ hκ x hx
  let ν := pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ
  let state := fun u=>pathHeatSectionwiseNativeWienerState (E:=E) (K:=K) ι c δ W (projIcc a b hab u)
  let kernel := fun u=>pathHeatSectionwiseNativeWienerKernel ι dc δ W (projIcc a b hab u)
  let weight := fun u ω=>d.weight (state u ω)
  let phi := fun u ω=>d.phi (state u ω)
  let H := fun u ω=>d.densityGenerator (kernel u) (state u ω)
  let J := fun u ω=>d.observableGenerator (kernel u) (state u ω)
  have hH (u : ℝ) (ω : pathHeatGeneralBaseSample E (Fin L) K) :
      df.densityGenerator (pathHeatWienerSourceKernel L (pathHeatTreeMixedKernelOperator δ W)
        (fun z=>pathHeatClockRawKernel (dc z)) (projIcc a b hab u))
        (pathHeatWienerSourceState L c (pathHeatTreeMixedOperator δ W) (projIcc a b hab u) ω)=H u ω :=
    pathHeatSectionwiseNativeSourceExtension_densityGenerator_continuousKernel ι d _ _
  have hJ (u : ℝ) (ω : pathHeatGeneralBaseSample E (Fin L) K) :
      df.observableGenerator (pathHeatWienerSourceKernel L (pathHeatTreeMixedKernelOperator δ W)
        (fun z=>pathHeatClockRawKernel (dc z)) (projIcc a b hab u))
        (pathHeatWienerSourceState L c (pathHeatTreeMixedOperator δ W) (projIcc a b hab u) ω)=J u ω :=
    pathHeatSectionwiseNativeSourceExtension_observableGenerator_continuousKernel ι d _ _
  have hR (u : ℝ) : pathHeatSectionwiseWienerResponse μ df c dc δ W (projIcc a b hab u)=
      pathHeatResponse ν (weight u) (phi u) (H u) (J u) := by
    unfold pathHeatSectionwiseWienerResponse
    simp_rw [hH,hJ]
    rfl
  have hL (u : ℝ) : pathHeatSectionwiseWienerLogNormalizerResponse μ df c dc δ W (projIcc a b hab u)=
      pathHeatExpectation ν (weight u) (H u) := by
    unfold pathHeatSectionwiseWienerLogNormalizerResponse
    simp_rw [hH]
    rfl
  have hE : HasDerivAt (fun u=>pathHeatExpectation ν (weight u) (phi u))
      (pathHeatResponse ν (weight x) (phi x) (H x) (J x)) x := by
    rw [←hR x]
    exact hd.2.1
  have hlog : HasDerivAt (fun u=>Real.log (pathHeatNormalizer ν (weight u)))
      (pathHeatExpectation ν (weight x) (H x)) x := by
    rw [←hL x]
    exact hd.2.2
  have hp (u : ℝ) : 0<pathHeatNormalizer ν (weight u) := by
    exact pathHeat_normalizer_positive (pathHeatSectionwiseWiener_actual_dominatedData
      μ hab df C hs c δ W (fun z=>pathHeatClockRawKernel (dc z)) κ hκ
      (projIcc a b hab u))
  have hcount := hasDerivAt_pathHeat_nat_counting_normalization ν weight phi H J
    (Fintype.card K) Fintype.card_ne_zero x hp hE hlog
  unfold pathHeatSectionwiseNativeWienerNormalizer pathHeatSectionwiseNativeWienerExpectation
    pathHeatSectionwiseNativeWienerResponse pathHeatSectionwiseNativeWienerLogNormalizerResponse
  rw [pathHeatGeneralCountMeasure_eq_card_smul_uniform μ]
  exact hcount

end HexagonPaper
