module
public import HexagonPaper.CavityTreePathTopology

@[expose] public section

/-! Actual pointwise parameter data and the native Stieltjes action agree
under the constructed tree charge. The terminal placeholder points carry
zero interior charge; no false pointwise equality there is asserted. -/
noncomputable section
open Set MeasureTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup
open scoped Topology
namespace HexagonPaper
open FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
variable {n : ℕ}

private theorem continuousMap_integrable_finite {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (f : C(X,ℝ)) (ν : Measure X) [IsFiniteMeasure ν] : Integrable f ν:=
  (BoundedContinuousFunction.mkOfCompact f).integrable ν

def treeNativePointPotential (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : ℕ→Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (x : AnisotropicObservationState n) (Z : Records (NativeTreePath n) (Configuration n) T):
    C(treePathWeightPoint T,ℝ):=
  (edgeTailPotentialMap D μ).comp
    ⟨treeNativePointData D q T x Z,continuous_treeNativePointData D q T x Z⟩

theorem treeNativePointPotential_action (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : ℕ→Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (x : AnisotropicObservationState n) (Z : Records (NativeTreePath n) (Configuration n) T):
    Integrable (treeNativeInteriorPotential D μ q T x Z) (treePathInteriorWeight μ q T) ∧
    (∫v,treeNativePointPotential D μ q T x Z v ∂treePathInteriorWeight μ q T)=
      ∫v,treeNativeInteriorPotential D μ q T x Z v ∂treePathInteriorWeight μ q T := by
  induction T generalizing x with
  | leaf=>exact ⟨integrable_const _,by simp only [treePathInteriorWeight,integral_zero_measure]⟩
  | @advance j T ih=>
    obtain ⟨hi,he⟩:=ih (edgePathEndpoint D (q j) Z.1) Z.2
    haveI:=isFiniteMeasure_treePathInteriorWeight μ q T
    have hp:=continuousMap_integrable_finite (treeNativePointPotential D μ q T
      (edgePathEndpoint D (q j) Z.1) Z.2) (treePathInteriorWeight μ q T)
    have hF:=continuousMap_integrable_probability (edgeNativePathPotential D μ Z.1) μ
    have ho:=treePathInteriorWeight_advance_integral μ q T
      (fun r=>anisotropicMeasureTailPotential D μ r (Z.1 r))
      (treeNativeInteriorPotential D μ q T (edgePathEndpoint D (q j) Z.1) Z.2)
      (edgeNativePathPotential D μ Z.1).continuous.measurable
      (measurable_treeNativeInteriorPotential D μ q T _ _) hF.restrict hi
    have hn:=treePathInteriorWeight_advance_integral μ q T
      (fun r=>anisotropicMeasureTailPotential D μ r (Z.1 r))
      (treeNativePointPotential D μ q T (edgePathEndpoint D (q j) Z.1) Z.2)
      (edgeNativePathPotential D μ Z.1).continuous.measurable
      (treeNativePointPotential D μ q T _ _).continuous.measurable hF.restrict hp
    refine ⟨ho.1,?_⟩
    have hfun : (fun v=>treeNativePointPotential D μ q (.advance T) x Z v)=
        Sum.elim (fun r=>anisotropicMeasureTailPotential D μ r (Z.1 r))
          (treeNativePointPotential D μ q T (edgePathEndpoint D (q j) Z.1) Z.2) := by
      funext v
      cases v <;> rfl
    rw [hfun]
    rw [hn.2,ho.2,he]
  | @fork j T U ihT ihU=>
    obtain ⟨hiT,heT⟩:=ihT x Z.1
    obtain ⟨hiU,heU⟩:=ihU x Z.2
    haveI:=isFiniteMeasure_treePathInteriorWeight μ q T
    haveI:=isFiniteMeasure_treePathInteriorWeight μ q U
    have hpT:=continuousMap_integrable_finite (treeNativePointPotential D μ q T x Z.1)
      (treePathInteriorWeight μ q T)
    have hpU:=continuousMap_integrable_finite (treeNativePointPotential D μ q U x Z.2)
      (treePathInteriorWeight μ q U)
    have ho:=treePathInteriorWeight_fork_integral μ q T U
      (anisotropicMeasureTailPotential D μ (q j) (anisotropicObservationParameter D x))
      (treeNativeInteriorPotential D μ q T x Z.1) (treeNativeInteriorPotential D μ q U x Z.2)
      (measurable_treeNativeInteriorPotential D μ q T x Z.1)
      (measurable_treeNativeInteriorPotential D μ q U x Z.2) hiT hiU
    have hn:=treePathInteriorWeight_fork_integral μ q T U
      (anisotropicMeasureTailPotential D μ (q j) (anisotropicObservationParameter D x))
      (treeNativePointPotential D μ q T x Z.1) (treeNativePointPotential D μ q U x Z.2)
      (treeNativePointPotential D μ q T x Z.1).continuous.measurable
      (treeNativePointPotential D μ q U x Z.2).continuous.measurable hpT hpU
    refine ⟨ho.1,?_⟩
    have hfun : (fun v=>treeNativePointPotential D μ q (.fork T U) x Z v)=
        Sum.elim (fun _:Unit=>anisotropicMeasureTailPotential D μ (q j)
          (anisotropicObservationParameter D x))
          (Sum.elim (treeNativePointPotential D μ q T x Z.1)
            (treeNativePointPotential D μ q U x Z.2)) := by
      funext v
      rcases v with (_|(_|_)) <;> rfl
    rw [hfun]
    rw [hn.2,ho.2,heT,heU]

theorem treeNativeFullPointData_action (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (hμ : μ∈scalarFloor a) (q : ℕ→Paper.Overlap) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (x : AnisotropicObservationState n)
    (Z : Records (NativeTreePath n) (Configuration n) T):
    (∫v,anisotropicMeasureTailPotential D μ (treeNativeFullPointData D q T x Z v).1
        (treeNativeFullPointData D q T x Z v).2 ∂treePathWeight μ a q T)=
      ∫v,treeNativeFullPotential D μ q T x Z v ∂treePathWeight μ a q T := by
  obtain ⟨hi,he⟩:=treeNativePointPotential_action D μ q T x Z
  haveI:=isFiniteMeasure_treePathInteriorWeight μ q T
  have hp:=continuousMap_integrable_finite (treeNativePointPotential D μ q T x Z)
    (treePathInteriorWeight μ q T)
  have ho:=treePathWeight_root_integral μ a hμ q T
    (anisotropicMeasureTailPotential D μ (q j) (anisotropicObservationParameter D x))
    (treeNativeInteriorPotential D μ q T x Z)
    (measurable_treeNativeInteriorPotential D μ q T x Z) hi
  have hn:=treePathWeight_root_integral μ a hμ q T
    (anisotropicMeasureTailPotential D μ (q j) (anisotropicObservationParameter D x))
    (treeNativePointPotential D μ q T x Z)
    (treeNativePointPotential D μ q T x Z).continuous.measurable hp
  have hfun : (fun v=>anisotropicMeasureTailPotential D μ (treeNativeFullPointData D q T x Z v).1
      (treeNativeFullPointData D q T x Z v).2)=
      Sum.elim (fun _:Unit=>anisotropicMeasureTailPotential D μ (q j)
        (anisotropicObservationParameter D x)) (treeNativePointPotential D μ q T x Z) := by
    funext v
    cases v <;> rfl
  rw [hfun]
  unfold treeNativeFullPotential
  rw [hn.2,ho.2,he]

end HexagonPaper
