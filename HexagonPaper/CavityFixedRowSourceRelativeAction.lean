module
public import HexagonPaper.CavityFixedRowSourceRelativeDensity

@[expose] public section

/-! At the genuine root level zero, the fixed-row source representative is
exactly the native root-plus-child source action difference. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper QuantitativeFollowup
namespace HexagonPaper
open FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
variable {n : ℕ}

theorem cavityNativeFixedRowSourceRelativeAction_eq_rootChild
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (hroot : q j = zeroOverlap) (θ : QuantitativePaper.Field n)
    (z : AnisotropicDisorder (n+1) ×
      Records (NativeTreePath (n+1)) (Configuration (n+1)) T) :
    cavityNativeFixedRowSourceRelativeAction D μ a q T θ z =
      treeNativeRootChildSourceRelativeAction (anisotropicUnitCouplings D) μ a q T
        (cavityNativeIncidentRow n θ) (z.1,0) z.2 := by
  unfold cavityNativeFixedRowSourceRelativeAction treeNativeRootChildSourceRelativeAction
    treeNativeRootChildSourceAction cavityNativeFixedRowPotential cavityNativeFixedRowShift
  simp only [hroot, zeroOverlap, anisotropicMeasureTailPotential_zero,
    cavityCouplingStartTranslation, anisotropicObservationParameter,
    map_zero, add_zero]
  ring

end HexagonPaper
