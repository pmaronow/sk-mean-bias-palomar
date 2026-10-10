module
public import HexagonPaper.PathHeatSectionwiseFiniteRaw
public import HexagonPaper.PathHeatWienerSourceLimit

@[expose] public section

/-! Exact transfer of the internally proved finite physical raw Price
derivatives to the common Wiener reference used by the limiting source
theorem. Compact-parameter clocks are extended only by projection. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped Topology BigOperators unitInterval NNReal BoundedContinuousFunction
namespace HexagonPaper
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Fintype K] [Nonempty K] [TopologicalSpace K] [DiscreteTopology K]
  [MeasurableSpace K] [BorelSpace K] [MeasurableSingletonClass K]
variable {L n : ℕ} {a b : ℝ}

theorem pathHeatSectionwise_finite_reordered_raw_derivatives
    (μ : Measure E) [IsGaussian μ]
    (hab : a≤b) (d : PathHeatSectionwiseSignedSource (Icc a b) E K (Fin L×I))
    (C : ℝ≥0) (hsource : PathHeatSectionwiseAnalyticSource a b hab d C)
    (c₀ : Icc a b→Fin L→C(I,I)) (dc₀ : Icc a b→Fin L→C(I,ℝ))
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ) (hn : n≠0)
    (hc : ∀q : Icc a b,q.val∈Ioo a b→∀l,StrictMono (c₀ q l))
    (hroot : ∀q l,c₀ q l 0=0)
    (hdc : ∀z∈Ioo a b,∀l t,
      HasDerivAt (fun u=>(c₀ (projIcc a b hab u) l t:ℝ))
        (dc₀ (projIcc a b hab z) l t) z)
    (hdcc : ∀l,Continuous (fun q=>dc₀ q l))
    (D : ℝ≥0) (hD : ∀q,‖pathHeatClockRawKernel (dc₀ q)‖≤D)
    (z : ℝ) (hz : z∈Ioo a b) :
    HasDerivAt
      (fun u=>∫ω,d.weight (pathHeatWienerSourceApproximateState L c₀
        (pathHeatTreeMixedOperator δ W) n (projIcc a b hab u) ω)
        ∂pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ)
      (∫ω,d.weight (pathHeatWienerSourceApproximateState L c₀
        (pathHeatTreeMixedOperator δ W) n (projIcc a b hab z) ω)*
        d.densityGenerator (pathHeatWienerSourceApproximateKernel L
          (pathHeatTreeMixedKernelOperator δ W) (fun q=>pathHeatClockRawKernel (dc₀ q))
          n (projIcc a b hab z))
          (pathHeatWienerSourceApproximateState L c₀ (pathHeatTreeMixedOperator δ W)
            n (projIcc a b hab z) ω)
        ∂pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ) z ∧
    HasDerivAt
      (fun u=>∫ω,d.weight (pathHeatWienerSourceApproximateState L c₀
        (pathHeatTreeMixedOperator δ W) n (projIcc a b hab u) ω)*
        d.phi (pathHeatWienerSourceApproximateState L c₀
          (pathHeatTreeMixedOperator δ W) n (projIcc a b hab u) ω)
        ∂pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ)
      (∫ω,d.weight (pathHeatWienerSourceApproximateState L c₀
        (pathHeatTreeMixedOperator δ W) n (projIcc a b hab z) ω)*
        (d.observableGenerator (pathHeatWienerSourceApproximateKernel L
          (pathHeatTreeMixedKernelOperator δ W) (fun q=>pathHeatClockRawKernel (dc₀ q))
          n (projIcc a b hab z))
          (pathHeatWienerSourceApproximateState L c₀ (pathHeatTreeMixedOperator δ W)
            n (projIcc a b hab z) ω)+
          d.phi (pathHeatWienerSourceApproximateState L c₀
            (pathHeatTreeMixedOperator δ W) n (projIcc a b hab z) ω)*
            d.densityGenerator (pathHeatWienerSourceApproximateKernel L
              (pathHeatTreeMixedKernelOperator δ W) (fun q=>pathHeatClockRawKernel (dc₀ q))
              n (projIcc a b hab z))
              (pathHeatWienerSourceApproximateState L c₀ (pathHeatTreeMixedOperator δ W)
                n (projIcc a b hab z) ω))
        ∂pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ) z := by
  let c := fun u=>c₀ (projIcc a b hab u)
  let dc := fun u=>dc₀ (projIcc a b hab u)
  let ν := pathHeatWienerMeshBase (J:=Fin L)
  let κ := (PMF.uniformOfFintype K).toMeasure
  have hraw := pathHeatSectionwise_finite_raw_derivatives μ κ hab d C hsource c dc δ W hn
    (fun u hu=>hc (projIcc a b hab u) (by
      simpa only [projIcc_of_mem hab (Ioo_subset_Icc_self hu)] using hu))
    (fun u=>hroot (projIcc a b hab u)) hdc
    (fun u hu l=>((hdcc l).comp continuous_projIcc).continuousAt)
    D (fun u _=>hD (projIcc a b hab u)) z hz
  have eqState (u : ℝ) (ω : pathHeatGeneralBaseSample E (Fin L) K) :
      pathHeatWienerFiniteConditionalState (n:=n) hab c δ W (ω.1.1,ω.2) u ω.1.2=
        pathHeatWienerSourceApproximateState L c₀ (pathHeatTreeMixedOperator δ W)
          n (projIcc a b hab u) ω := rfl
  have eqKernel (u : ℝ) :
      pathHeatWienerFiniteKernel n L δ W dc u=
        pathHeatWienerSourceApproximateKernel L (pathHeatTreeMixedKernelOperator δ W)
          (fun q=>pathHeatClockRawKernel (dc₀ q)) n (projIcc a b hab u) := rfl
  have eqZ (u : ℝ) :
      (∫ω,d.weight (pathHeatWienerSourceApproximateState L c₀ (pathHeatTreeMixedOperator δ W)
        n (projIcc a b hab u) ω)∂pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ)=
      (∫ω,d.weight (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W ω.1 u ω.2)
        ∂(μ.prod κ).prod ν) := by
    simpa only [pathHeatGeneralUniformMeasure,ν,pathHeatWienerMeshBase,κ,eqState] using
      pathHeatReferenceReorder_integral μ ν κ
        (fun ω=>d.weight (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W ω.1 u ω.2))
  have eqN (u : ℝ) :
      (∫ω,d.weight (pathHeatWienerSourceApproximateState L c₀ (pathHeatTreeMixedOperator δ W)
        n (projIcc a b hab u) ω)*d.phi (pathHeatWienerSourceApproximateState L c₀
          (pathHeatTreeMixedOperator δ W) n (projIcc a b hab u) ω)
        ∂pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ)=
      (∫ω,d.weight (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W ω.1 u ω.2)*
        d.phi (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W ω.1 u ω.2)
        ∂(μ.prod κ).prod ν) := by
    simpa only [pathHeatGeneralUniformMeasure,ν,pathHeatWienerMeshBase,κ,eqState] using
      pathHeatReferenceReorder_integral μ ν κ
        (fun ω=>d.weight (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W ω.1 u ω.2)*
          d.phi (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W ω.1 u ω.2))
  have eqDZ :
      (∫ω,d.weight (pathHeatWienerSourceApproximateState L c₀ (pathHeatTreeMixedOperator δ W)
        n (projIcc a b hab z) ω)*
        d.densityGenerator (pathHeatWienerSourceApproximateKernel L (pathHeatTreeMixedKernelOperator δ W)
          (fun q=>pathHeatClockRawKernel (dc₀ q)) n (projIcc a b hab z))
          (pathHeatWienerSourceApproximateState L c₀ (pathHeatTreeMixedOperator δ W)
            n (projIcc a b hab z) ω)
        ∂pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ)=
      (∫ω,d.weight (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W ω.1 z ω.2)*
        d.densityGenerator (pathHeatWienerFiniteKernel n L δ W dc z)
          (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W ω.1 z ω.2)
        ∂(μ.prod κ).prod ν) := by
    simpa only [pathHeatGeneralUniformMeasure,ν,pathHeatWienerMeshBase,κ,eqState,eqKernel] using
      pathHeatReferenceReorder_integral μ ν κ
        (fun ω=>d.weight (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W ω.1 z ω.2)*
          d.densityGenerator (pathHeatWienerFiniteKernel n L δ W dc z)
            (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W ω.1 z ω.2))
  have eqDN :
      (∫ω,d.weight (pathHeatWienerSourceApproximateState L c₀ (pathHeatTreeMixedOperator δ W)
        n (projIcc a b hab z) ω)*
        (d.observableGenerator (pathHeatWienerSourceApproximateKernel L (pathHeatTreeMixedKernelOperator δ W)
          (fun q=>pathHeatClockRawKernel (dc₀ q)) n (projIcc a b hab z))
          (pathHeatWienerSourceApproximateState L c₀ (pathHeatTreeMixedOperator δ W)
            n (projIcc a b hab z) ω)+
          d.phi (pathHeatWienerSourceApproximateState L c₀ (pathHeatTreeMixedOperator δ W)
            n (projIcc a b hab z) ω)*
            d.densityGenerator (pathHeatWienerSourceApproximateKernel L (pathHeatTreeMixedKernelOperator δ W)
              (fun q=>pathHeatClockRawKernel (dc₀ q)) n (projIcc a b hab z))
              (pathHeatWienerSourceApproximateState L c₀ (pathHeatTreeMixedOperator δ W)
                n (projIcc a b hab z) ω))
        ∂pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ)=
      (∫ω,d.weight (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W ω.1 z ω.2)*
        (d.observableGenerator (pathHeatWienerFiniteKernel n L δ W dc z)
          (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W ω.1 z ω.2)+
          d.phi (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W ω.1 z ω.2)*
            d.densityGenerator (pathHeatWienerFiniteKernel n L δ W dc z)
              (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W ω.1 z ω.2))
        ∂(μ.prod κ).prod ν) := by
    simpa only [pathHeatGeneralUniformMeasure,ν,pathHeatWienerMeshBase,κ,eqState,eqKernel] using
      pathHeatReferenceReorder_integral μ ν κ
        (fun ω=>d.weight (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W ω.1 z ω.2)*
          (d.observableGenerator (pathHeatWienerFiniteKernel n L δ W dc z)
            (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W ω.1 z ω.2)+
            d.phi (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W ω.1 z ω.2)*
              d.densityGenerator (pathHeatWienerFiniteKernel n L δ W dc z)
                (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W ω.1 z ω.2)))
  constructor
  · rw [eqDZ]
    exact hraw.1.congr_of_eventuallyEq (.of_forall eqZ)
  · rw [eqDN]
    exact hraw.2.congr_of_eventuallyEq (.of_forall eqN)

end HexagonPaper
