module
public import HexagonPaper.PathHeatWienerFiniteEnvelope
public import HexagonPaper.PathHeatAuxiliaryWienerRaw

@[expose] public section

/-! Source-facing finite raw derivatives on the actual physical Wiener
reference, including untouched Gaussian and finite counting coordinates.
All conditional Price, measurability and domination data are proved here. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped Topology BigOperators unitInterval NNReal BoundedContinuousFunction
namespace HexagonPaper
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Fintype K] [TopologicalSpace K] [DiscreteTopology K]
  [MeasurableSpace K] [BorelSpace K] [MeasurableSingletonClass K]
variable {L n : ℕ} {a b : ℝ}

theorem pathHeatWiener_finite_raw_derivatives
    (μ : Measure E) [IsGaussian μ] (κ : Measure K) [IsFiniteMeasure κ]
    (hab : a≤b) (d : PathHeatContinuousSignedSource (Icc a b×((E×K)×C(Fin L×I,ℝ))) (Fin L×I))
    (C : ℝ≥0) (hsource : PathHeatWienerAnalyticSource a b hab d C)
    (c : ℝ→Fin L→C(I,I)) (dc : ℝ→Fin L→C(I,ℝ))
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ) (hn : n≠0)
    (hc : ∀z∈Ioo a b,∀l,StrictMono (c z l))
    (hroot : ∀z l,c z l 0=0)
    (hdc : ∀z∈Ioo a b,∀l t,HasDerivAt (fun u=>(c u l t:ℝ)) (dc z l t) z)
    (hdcc : ∀z∈Ioo a b,∀l,ContinuousAt (fun u=>dc u l) z)
    (D : ℝ≥0) (hD : ∀z∈Ioo a b,‖pathHeatClockRawKernel (dc z)‖≤D)
    (z : ℝ) (hz : z∈Ioo a b) :
    HasDerivAt
      (fun u=>∫ω,d.weight (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W ω.1 u ω.2)
        ∂(μ.prod κ).prod (pathHeatWienerMeshBase (J:=Fin L)))
      (∫ω,d.weight (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W ω.1 z ω.2)*
        d.densityGenerator (pathHeatWienerFiniteKernel n L δ W dc z)
          (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W ω.1 z ω.2)
        ∂(μ.prod κ).prod (pathHeatWienerMeshBase (J:=Fin L))) z ∧
    HasDerivAt
      (fun u=>∫ω,d.weight (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W ω.1 u ω.2)*
        d.phi (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W ω.1 u ω.2)
        ∂(μ.prod κ).prod (pathHeatWienerMeshBase (J:=Fin L)))
      (∫ω,d.weight (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W ω.1 z ω.2)*
        (d.observableGenerator (pathHeatWienerFiniteKernel n L δ W dc z)
          (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W ω.1 z ω.2)+
          d.phi (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W ω.1 z ω.2)*
            d.densityGenerator (pathHeatWienerFiniteKernel n L δ W dc z)
              (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W ω.1 z ω.2))
        ∂(μ.prod κ).prod (pathHeatWienerMeshBase (J:=Fin L))) z := by
  let state := fun u (ω : (E×K)×(Fin L→WienerPath))=>
    pathHeatWienerFiniteConditionalState (n:=n) hab c δ W ω.1 u ω.2
  let weight := fun u ω=>d.weight (state u ω)
  let phi := fun u ω=>d.phi (state u ω)
  let H := fun u ω=>d.densityGenerator (pathHeatWienerFiniteKernel n L δ W dc u) (state u ω)
  let J := fun u ω=>d.observableGenerator (pathHeatWienerFiniteKernel n L δ W dc u) (state u ω)
  let bound : ℝ≥0 := Real.toNNReal ((pathHeatTreeMixedBound δ W)^2*(D:ℝ))
  let envelope := pathHeatWienerConditionalEnvelope (L:=L) (E:=E) (K:=K)
    (C*(1+pathHeatTreeMixedBound δ W))
  have hs (u : ℝ) : Continuous (state u) := continuous_pathHeatWienerFiniteConditionalState hab c δ W u
  have hweight (u : ℝ) : Continuous (weight u) := d.continuous_weight.comp (hs u)
  have hphi (u : ℝ) : Continuous (phi u) := d.continuous_phi.comp (hs u)
  have hH (u : ℝ) : Continuous (H u) := (d.continuous_densityGenerator _).comp (hs u)
  have hJ (u : ℝ) : Continuous (J u) := (d.continuous_observableGenerator _).comp (hs u)
  apply pathHeat_auxiliary_Wiener_raw_derivatives (μ.prod κ)
    (pathHeatWienerMeshBase (J:=Fin L)) (Ioo a b) z (isOpen_Ioo.mem_nhds hz)
    weight phi H J envelope d.B (d.densityBound bound) (d.observableBound bound)
    d.B.coe_nonneg (d.densityBound_nonneg bound) (d.observableBound_nonneg bound)
  · exact integrable_pathHeatWienerConditionalEnvelope μ κ _
  · exact integrable_pathHeatWienerConditionalEnvelope_slice _
  · intro ω
    exact (Real.exp_pos _).le
  · intro u hu
    exact (hweight u).stronglyMeasurable
  · intro u hu
    exact ((hweight u).mul (hphi u)).stronglyMeasurable
  · intro u hu
    exact ((hweight u).mul (hH u)).stronglyMeasurable
  · intro u hu
    exact ((hweight u).mul ((hJ u).add ((hphi u).mul (hH u)))).stronglyMeasurable
  · intro u hu ω
    have hk := norm_pathHeatWienerFiniteKernel_le (n:=n) δ W dc D u (hD u hu)
    exact ⟨(Real.exp_pos _).le,
      pathHeatWienerFinite_weight_bound hab d C hsource c δ W u ω.1 ω.2,
      d.bound_phi _,d.densityGenerator_bound _ bound hk _,d.observableGenerator_bound _ bound hk _⟩
  · intro aux u hu
    exact (pathHeatWiener_finite_conditional_derivatives hab d C hsource c dc δ W hn
      hc hroot hdc hdcc aux u hu).2.1
  · intro aux u hu
    exact (pathHeatWiener_finite_conditional_derivatives hab d C hsource c dc δ W hn
      hc hroot hdc hdcc aux u hu).2.2

end HexagonPaper
