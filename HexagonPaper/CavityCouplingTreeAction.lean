module
public import HexagonPaper.CavityCouplingTreeActionBasic

@[expose] public section

/-! Literal root-plus-child native source action and its exact coupling
change, integrated against the unchanged positive full tree charge. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup FiniteTerminalGenealogy
open scoped Topology ENNReal
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def treeNativeRootChildSourceAction (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (q : ℕ→Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (x : AnisotropicObservationState n) (Z : Records (NativeTreePath n) (Configuration n) T) : ℝ :=
  a*anisotropicMeasureTailPotential D μ (q j) (anisotropicObservationParameter D x)+
    treeNativeSourceLog D μ q T x Z

def treeNativeRootChildSourceRelativeAction (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (h : AnisotropicDisorder n)
    (x : AnisotropicObservationState n) (Z : Records (NativeTreePath n) (Configuration n) T) : ℝ :=
  treeNativeRootChildSourceAction D μ a q T (cavityCouplingStartTranslation h x)
    (cavityTreeRecordPathMap (cavityCouplingPathTranslation h) T Z)-
    treeNativeRootChildSourceAction D μ a q T x Z

theorem treeNativeRootChildSourceAction_eq_point_integral (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (hμ : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (h0 : q 0=1) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (x : AnisotropicObservationState n) (Z : Records (NativeTreePath n) (Configuration n) T) :
    treeNativeRootChildSourceAction D μ a q T x Z=treeNativeTerminalEnergy D q T x Z-
      ∫v,anisotropicMeasureTailPotential D μ (treeNativeFullPointData D q T x Z v).1
        (treeNativeFullPointData D q T x Z v).2 ∂treePathWeight μ a q T := by
  unfold treeNativeRootChildSourceAction
  rw [treeNativeFullPointData_action D μ a hμ q T x Z]
  exact (treeNativeSourceLog_full_weight D μ a hμ q h0 T x Z).2

theorem treeNativeRootChildSourceRelativeAction_eq_increment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (hμ : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (h0 : q 0=1) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (h : AnisotropicDisorder n) (x : AnisotropicObservationState n)
    (Z : Records (NativeTreePath n) (Configuration n) T) :
    treeNativeRootChildSourceRelativeAction D μ a q T h x Z=
      treeNativeCouplingTerminalIncrement D h T Z-
      ∫v,(anisotropicMeasureTailPotential D μ (treeNativeFullPointData D q T x Z v).1
          ((treeNativeFullPointData D q T x Z v).2+anisotropicDisorderInjection n h)-
        anisotropicMeasureTailPotential D μ (treeNativeFullPointData D q T x Z v).1
          (treeNativeFullPointData D q T x Z v).2) ∂treePathWeight μ a q T := by
  letI:=isFiniteMeasure_treePathWeight μ a q T
  let A : C(Unit⊕treePathWeightPoint T,ℝ):=(edgeTailPotentialMap D μ).comp
    (treeNativeFullPointData D q T x Z)
  let B : C(Unit⊕treePathWeightPoint T,ℝ):=(edgeTailPotentialMap D μ).comp
    (treeNativeFullPointData D q T (cavityCouplingStartTranslation h x)
      (cavityTreeRecordPathMap (cavityCouplingPathTranslation h) T Z))
  have hA : Integrable A (treePathWeight μ a q T):=
    (BoundedContinuousFunction.mkOfCompact A).integrable _
  have hB : Integrable B (treePathWeight μ a q T):=
    (BoundedContinuousFunction.mkOfCompact B).integrable _
  have hb : ∀v,B v=anisotropicMeasureTailPotential D μ
      (treeNativeFullPointData D q T x Z v).1
      ((treeNativeFullPointData D q T x Z v).2+anisotropicDisorderInjection n h):=by
    intro v
    change anisotropicMeasureTailPotential D μ _ _=_
    rw [treeNativeFullPointData_coupling_translation D q h T x Z v]
  unfold treeNativeRootChildSourceRelativeAction
  rw [treeNativeRootChildSourceAction_eq_point_integral D μ a hμ q h0,
    treeNativeRootChildSourceAction_eq_point_integral D μ a hμ q h0]
  change (treeNativeTerminalEnergy D q T (cavityCouplingStartTranslation h x)
    (cavityTreeRecordPathMap (cavityCouplingPathTranslation h) T Z)-∫v,B v∂treePathWeight μ a q T)-
    (treeNativeTerminalEnergy D q T x Z-∫v,A v∂treePathWeight μ a q T)=_
  have ht:=treeNativeTerminalEnergy_coupling_translation D q h T x Z
  have hi : (∫v,B v∂treePathWeight μ a q T)-(∫v,A v∂treePathWeight μ a q T)=
      ∫v,(anisotropicMeasureTailPotential D μ (treeNativeFullPointData D q T x Z v).1
          ((treeNativeFullPointData D q T x Z v).2+anisotropicDisorderInjection n h)-
        anisotropicMeasureTailPotential D μ (treeNativeFullPointData D q T x Z v).1
          (treeNativeFullPointData D q T x Z v).2) ∂treePathWeight μ a q T := by
    rw [←integral_sub hB hA]
    apply integral_congr_ae
    exact .of_forall fun v=>by
      change B v-A v=_
      rw [hb v]
      rfl
  linear_combination ht-hi

end HexagonPaper
