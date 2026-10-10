module
public import HexagonPaper.PathHeatWienerFiniteEnvelope
public import HexagonPaper.PathHeatSectionwiseConditionalResponse
public import HexagonPaper.PathHeatSectionwiseWienerData
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
  [Fintype K] [Nonempty K] [TopologicalSpace K] [DiscreteTopology K]
  [MeasurableSpace K] [BorelSpace K] [MeasurableSingletonClass K]
variable {L n : ℕ} {a b : ℝ}
local instance instSectionwiseFiniteRawPathMeasurable : MeasurableSpace C(Fin L×I,ℝ) := borel _
local instance instSectionwiseFiniteRawPathBorel : BorelSpace C(Fin L×I,ℝ) := ⟨rfl⟩

theorem pathHeatSectionwiseFinite_weight_bound (hab : a≤b)
    (d : PathHeatSectionwiseSignedSource (Icc a b) E K (Fin L×I))
    (C : ℝ≥0) (hsource : PathHeatSectionwiseAnalyticSource a b hab d C)
    (c : ℝ→Fin L→C(I,I)) (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (z : ℝ) (aux : E×K) (w : Fin L→WienerPath) :
    d.weight (pathHeatWienerFiniteConditionalState (n:=n) hab c δ W aux z w)≤
      pathHeatWienerConditionalEnvelope (C*(1+pathHeatTreeMixedBound δ W)) (aux,w) := by
  let T := pathHeatTreeMixedOperator (E:=ℝ) δ W
  let p := T (pathHeatTreeBernsteinOperator n L (pathHeatFlatClockPath L (c z) w))
  have hp : ‖p‖≤pathHeatTreeMixedBound δ W*(∑l : Fin L,‖w l‖) :=
    (pathHeatTreeMixedOperator_norm_apply_le δ W _).trans (mul_le_mul_of_nonneg_left
      ((norm_pathHeatTreeBernsteinSample_le n L _).trans (norm_pathHeatFlatClockPath_le L _ _))
      (pathHeatTreeMixedBound_nonneg δ W))
  have hsum : 0≤∑l : Fin L,‖w l‖ := Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  have hg := (le_abs_self (d.ell (projIcc a b hab z,(aux,p)))).trans
    (hsource.ell_growth (projIcc a b hab z) aux p)
  change Real.exp (d.ell (projIcc a b hab z,(aux,p)))≤
    Real.exp (C*(1+pathHeatTreeMixedBound δ W)*(1+‖aux.1‖+∑l : Fin L,‖w l‖))
  apply Real.exp_le_exp.mpr
  have hC : 0≤(C:ℝ) := C.coe_nonneg
  nlinarith [norm_nonneg aux.1,pathHeatTreeMixedBound_nonneg δ W,
    mul_nonneg hC (pathHeatTreeMixedBound_nonneg δ W),mul_nonneg hC hsum,
    mul_nonneg (mul_nonneg hC (pathHeatTreeMixedBound_nonneg δ W)) (norm_nonneg aux.1)]


theorem pathHeatSectionwise_finite_raw_derivatives
    (μ : Measure E) [IsGaussian μ] (κ : Measure K) [IsFiniteMeasure κ]
    (hab : a≤b) (d : PathHeatSectionwiseSignedSource (Icc a b) E K (Fin L×I))
    (C : ℝ≥0) (hsource : PathHeatSectionwiseAnalyticSource a b hab d C)
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
  have hH (u : ℝ) : Measurable (H u) :=
    (measurable_pathHeatSectionwiseDensityGenerator_mixedKernel hab d C hsource δ W
      (pathHeatTreeKernelSample n L (pathHeatClockRawKernel (dc u)))).comp (hs u).measurable
  have hJ (u : ℝ) : Measurable (J u) :=
    (measurable_pathHeatSectionwiseObservableGenerator_mixedKernel hab d C hsource δ W
      (pathHeatTreeKernelSample n L (pathHeatClockRawKernel (dc u)))).comp (hs u).measurable
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
    exact ((hweight u).measurable.mul (hH u)).stronglyMeasurable
  · intro u hu
    exact ((hweight u).measurable.mul ((hJ u).add ((hphi u).measurable.mul (hH u)))).stronglyMeasurable
  · intro u hu ω
    have hk := norm_pathHeatWienerFiniteKernel_le (n:=n) δ W dc D u (hD u hu)
    exact ⟨(Real.exp_pos _).le,
      pathHeatSectionwiseFinite_weight_bound hab d C hsource c δ W u ω.1 ω.2,
      d.bound_phi _,d.densityGenerator_bound _ bound hk _,d.observableGenerator_bound _ bound hk _⟩
  · intro aux u hu
    exact (pathHeatSectionwise_finite_conditional_derivatives hab d C hsource c dc δ W hn
      hc hroot hdc hdcc aux u hu).2.1
  · intro aux u hu
    exact (pathHeatSectionwise_finite_conditional_derivatives hab d C hsource c dc δ W hn
      hc hroot hdc hdcc aux u hu).2.2

end HexagonPaper
