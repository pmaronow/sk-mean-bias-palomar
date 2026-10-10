module
public import HexagonPaper.PathHeatWeakKernelMeasurable
public import HexagonPaper.PathHeatSectionwiseJetMeasurable
public import HexagonPaper.PathHeatWienerSourceLimit
public import HexagonPaper.PathHeatWienerDifferentiation

@[expose] public section

/-! Actual common-Wiener dominated data from the weakest auxiliary source
regularity. Scalar weak measurability is derived from genuine spatial jets;
finite-rank covariance contractions give generator measurability. Only
fixed-auxiliary TV continuity is used elsewhere in the moving limits. -/
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
variable {L : ℕ} {a b : ℝ}

local instance instSectionwiseWienerDataPathMeasurable : MeasurableSpace C(Fin L×I,ℝ) := borel _
local instance instSectionwiseWienerDataPathBorel : BorelSpace C(Fin L×I,ℝ) := ⟨rfl⟩

 theorem measurable_pathHeatSectionwiseDensityGenerator_mixedKernel
    (hab : a≤b) (d : PathHeatSectionwiseSignedSource (Icc a b) E K (Fin L×I))
    (C : ℝ≥0) (hs : PathHeatSectionwiseAnalyticSource a b hab d C)
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ) (D : C(Fin L×I,C(Fin L×I,ℝ))) :
    Measurable (d.densityGenerator (pathHeatTreeKernelBCF L (pathHeatTreeMixedKernelOperator δ W D))) :=
  measurable_pathHeatDensityGenerator_mixedKernel d.S d.M d.dotell
    (measurable_pathHeatSectionwise_score hab d C hs)
    (measurable_pathHeatSectionwise_hessian hab d C hs) d.continuous_dotell.measurable δ W D

 theorem measurable_pathHeatSectionwiseObservableGenerator_mixedKernel
    (hab : a≤b) (d : PathHeatSectionwiseSignedSource (Icc a b) E K (Fin L×I))
    (C : ℝ≥0) (hs : PathHeatSectionwiseAnalyticSource a b hab d C)
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ) (D : C(Fin L×I,C(Fin L×I,ℝ))) :
    Measurable (d.observableGenerator (pathHeatTreeKernelBCF L (pathHeatTreeMixedKernelOperator δ W D))) :=
  measurable_pathHeatObservableGenerator_mixedKernel d.S d.P d.Q d.dotphi
    (measurable_pathHeatSectionwise_score hab d C hs)
    (measurable_pathHeatSectionwise_phi_score hab d C hs)
    (measurable_pathHeatSectionwise_phi_hessian hab d C hs) d.continuous_dotphi.measurable δ W D

 theorem pathHeatSectionwiseWiener_dominatedData
    (μ : Measure E) [IsGaussian μ]
    (hab : a≤b) (d : PathHeatSectionwiseSignedSource (Icc a b) E K (Fin L×I))
    (C : ℝ≥0) (hs : PathHeatSectionwiseAnalyticSource a b hab d C)
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (D : C(Fin L×I,C(Fin L×I,ℝ))) (κ : ℝ≥0) (hD : ‖D‖≤κ)
    (R : ℝ) (hR : 0≤R) (p : pathHeatGeneralBaseSample E (Fin L) K→C(Fin L×I,ℝ))
    (hp : Measurable p) (hpn : ∀ω,‖p ω‖≤R*∑l,‖ω.1.2 l‖) (z : Icc a b) :
    let state := fun ω=>(z,((ω.1.1,ω.2),p ω))
    let kernel := pathHeatTreeKernelBCF L (pathHeatTreeMixedKernelOperator δ W D)
    PathHeatDominatedData (pathHeatGeneralUniformMeasure (J:=Fin L) (K:=K) μ)
      (fun ω=>d.weight (state ω)) (fun ω=>d.phi (state ω))
      (fun ω=>d.densityGenerator kernel (state ω)) (fun ω=>d.observableGenerator kernel (state ω))
      (pathHeatGeneralEnvelope (C*(1+R))) d.B
      (d.densityBound (pathHeatWienerMixedKernelBound δ W*κ))
      (d.observableBound (pathHeatWienerMixedKernelBound δ W*κ)) := by
  dsimp only
  let state := fun ω : pathHeatGeneralBaseSample E (Fin L) K=>(z,((ω.1.1,ω.2),p ω))
  let kernel := pathHeatTreeKernelBCF L (pathHeatTreeMixedKernelOperator δ W D)
  let κN := pathHeatWienerMixedKernelBound δ W*κ
  have hstate : Measurable state := measurable_const.prodMk ((measurable_fst.fst.prodMk measurable_snd).prodMk hp)
  have hK : ‖kernel‖≤κN :=
    (norm_pathHeatTreeKernelBCF_le L _).trans
      ((norm_pathHeatTreeMixedKernelOperator_apply_le δ W D).trans
        (mul_le_mul_of_nonneg_left hD (sq_nonneg _)))
  have hweight := d.continuous_weight.measurable.comp hstate
  have hphi := d.continuous_phi.measurable.comp hstate
  have hH := (measurable_pathHeatSectionwiseDensityGenerator_mixedKernel hab d C hs δ W D).comp hstate
  have hJ := (measurable_pathHeatSectionwiseObservableGenerator_mixedKernel hab d C hs δ W D).comp hstate
  have hb : ∀ω,d.weight (state ω)≤pathHeatGeneralEnvelope (C*(1+R)) ω := by
    apply pathHeatGeneral_linearGrowth_envelope p (fun ω=>d.ell (state ω)) C R C.coe_nonneg hR hpn
    intro ω
    exact hs.ell_growth z (ω.1.1,ω.2) (p ω)
  exact ⟨integrable_pathHeatGeneralEnvelope_uniform (J:=Fin L) (K:=K) μ _,
    d.B.coe_nonneg,d.densityBound_nonneg κN,d.observableBound_nonneg κN,
    hweight.aestronglyMeasurable,hphi.aestronglyMeasurable,hH.aestronglyMeasurable,hJ.aestronglyMeasurable,
    .of_forall (fun ω=>Real.exp_pos _),.of_forall hb,.of_forall (fun ω=>d.bound_phi _),
    .of_forall (fun ω=>d.densityGenerator_bound kernel κN hK _),
    .of_forall (fun ω=>d.observableGenerator_bound kernel κN hK _)⟩

end HexagonPaper
