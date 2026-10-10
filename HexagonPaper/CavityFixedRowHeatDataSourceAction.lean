module
public import HexagonPaper.CavityFixedRowHeatDataActionEnvelope
public import HexagonPaper.CavityFixedRowHeatDataTerminal
public import HexagonPaper.CavityFixedRowSourceRelativeAction

@[expose] public section

/-! Genuine fixed-row native source action has a uniform exponential
second-jet envelope against the actual baseline full-tree probability. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup FiniteTerminalGenealogy
open scoped Topology ContDiff BigOperators
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

def cavityNativeFixedRowParameterChart (n : ℕ) : Field n→L[ℝ]AnisotropicParameter (n+1) :=
  (anisotropicDisorderInjection (n+1)).comp (cavityNativeIncidentRow n)

theorem cavityNativeFixedRowSourceRelativeAction_eq_charge
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ) (hμ : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (h0 : q 0=1) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (hroot : q j=zeroOverlap) (θ : Field n)
    (z : AnisotropicDisorder (n+1)×Records (NativeTreePath (n+1)) (Configuration (n+1)) T) :
    cavityNativeFixedRowSourceRelativeAction D μ a q T θ z=
      cavityNativeChargeRelativeAction D μ (treePathWeight μ a q T)
        (treeNativeFullPointData (anisotropicUnitCouplings D) q T (z.1,0) z.2)
        (cavityNativeFixedRowParameterChart n)
        (cavityTreeTerminalIncrementLinear (anisotropicUnitCouplings D)
          (cavityNativeFixedRowParameterChart n) T z.2) θ := by
  let ν:=treePathWeight μ a q T
  letI:=isFiniteMeasure_treePathWeight μ a q T
  let A : C(Unit⊕treePathWeightPoint T,Paper.Overlap×AnisotropicParameter (n+1)):=treeNativeFullPointData (anisotropicUnitCouplings D) q T (z.1,0) z.2
  let L : Field n→L[ℝ]AnisotropicParameter (n+1):=cavityNativeFixedRowParameterChart n
  have ht : Continuous (fun v:Unit⊕treePathWeightPoint T=>((A v).1,(A v).2+L θ)):=
    A.continuous.fst.prodMk (A.continuous.snd.add continuous_const)
  have hc : Continuous (fun v:Unit⊕treePathWeightPoint T=>
      anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ (A v).1 ((A v).2+L θ)):=by
    have hh:=(continuous_anisotropicMeasureTailPotential_joint (anisotropicUnitCouplings D) μ).comp ht
    apply hh.congr
    intro v
    rfl
  let B : C(Unit⊕treePathWeightPoint T,ℝ):=
    ⟨fun v=>anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ (A v).1 ((A v).2+L θ),hc⟩
  let C : C(Unit⊕treePathWeightPoint T,ℝ):=
    (edgeTailPotentialMap (anisotropicUnitCouplings D) μ).comp A
  have hiB : Integrable B ν:=(BoundedContinuousFunction.mkOfCompact B).integrable _
  have hiC : Integrable C ν:=(BoundedContinuousFunction.mkOfCompact C).integrable _
  rw [cavityNativeFixedRowSourceRelativeAction_eq_rootChild D μ a q T hroot,
    treeNativeRootChildSourceRelativeAction_eq_increment (anisotropicUnitCouplings D) μ a hμ q h0]
  rw [←cavityTreeTerminalIncrementLinear_eq_native (anisotropicUnitCouplings D) (cavityNativeIncidentRow n)]
  unfold cavityNativeChargeRelativeAction cavityNativeChargePotential
  simp only [map_zero,add_zero]
  change (cavityTreeTerminalIncrementLinear (anisotropicUnitCouplings D) L T z.2) θ-
    (∫v,B v-C v∂ν)=(cavityTreeTerminalIncrementLinear (anisotropicUnitCouplings D) L T z.2) θ-
      ((∫v,B v∂ν)-(∫v,C v∂ν))
  exact congrArg (fun t=>(cavityTreeTerminalIncrementLinear (anisotropicUnitCouplings D) L T z.2) θ-t)
    (integral_sub hiB hiC)

 theorem cavityNativeFixedRowSourceRelativeAction_smooth
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ) (hμ : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (h0 : q 0=1) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (hroot : q j=zeroOverlap)
    (z : AnisotropicDisorder (n+1)×Records (NativeTreePath (n+1)) (Configuration (n+1)) T) :
    ContDiff ℝ ∞ (fun θ=>cavityNativeFixedRowSourceRelativeAction D μ a q T θ z) := by
  letI:=isFiniteMeasure_treePathWeight μ a q T
  have he:=funext (fun θ=>cavityNativeFixedRowSourceRelativeAction_eq_charge D μ a hμ q h0 T hroot θ z)
  rw [he]
  exact cavityNativeChargeRelativeAction_smooth D μ _ _ _ _

 theorem cavityNativeFixedRowSourceRelativeAction_exp_uniform_two_jets
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ) (hμ : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (h0 : q 0=1) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (hroot : q j=zeroOverlap) :
    ∃C R : ℝ,0 ≤ C ∧ 0 ≤ R ∧ ∀r,r ≤ 2→∀θ z,
      ‖iteratedFDeriv ℝ r (fun y=>Real.exp (cavityNativeFixedRowSourceRelativeAction D μ a q T y z)) θ‖ ≤
        C*Real.exp (R*‖θ‖) := by
  letI:=isFiniteMeasure_treePathWeight μ a q T
  let L : Field n→L[ℝ]AnisotropicParameter (n+1):=cavityNativeFixedRowParameterChart n
  let b:=max 1 (cavityTreeTerminalIncrementBound (anisotropicUnitCouplings D) L T)
  obtain ⟨C,R,hC,hR,hb⟩:=cavityNativeChargeRelativeAction_exp_uniform_two_jets D μ
    (treePathWeight μ a q T) L b (le_max_left _ _)
  refine ⟨C,R,hC,hR,?_⟩
  intro r hr θ z
  simp_rw [cavityNativeFixedRowSourceRelativeAction_eq_charge D μ a hμ q h0 T hroot]
  exact hb _ _ ((cavityTreeTerminalIncrementLinear_norm_le (anisotropicUnitCouplings D) L T z.2).trans
    (le_max_right _ _)) r hr θ

end HexagonPaper
