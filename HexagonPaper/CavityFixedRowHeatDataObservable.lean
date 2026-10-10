module
public import HexagonPaper.CavityFixedRowJetsBounds
public import HexagonPaper.CavityFixedRowHeatDataSourceAction
public import HexagonPaper.CavityVertexCancellationTreeConditional

@[expose] public section

/-! Actual retained full-tree last and rest self-overlaps. Their dependence
on the incident row is the genuine affine native field chart. -/
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

def cavityNativeFixedRowTaggedField (D : AnisotropicSpinModel (n+1)) (q : ℕ→Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (v : Unit⊕treePathWeightPoint T)
    (z : AnisotropicDisorder (n+1)×Records (NativeTreePath (n+1)) (Configuration (n+1)) T) :
    AnisotropicParameter (n+1):=
  (treeNativeFullPointData (anisotropicUnitCouplings D) q T (z.1,0) z.2 v).2

 theorem measurable_cavityNativeFixedRowTaggedField (D : AnisotropicSpinModel (n+1))
    (q : ℕ→Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j) (v : Unit⊕treePathWeightPoint T):
    Measurable (cavityNativeFixedRowTaggedField D q T v) :=
  (measurable_treeNativeFullPointData_field (anisotropicUnitCouplings D) q T v).comp
    ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)

 theorem cavityNativeFixedRowTaggedField_shift (D : AnisotropicSpinModel (n+1))
    (q : ℕ→Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j) (v : Unit⊕treePathWeightPoint T)
    (θ : Field n) (z : AnisotropicDisorder (n+1)×Records (NativeTreePath (n+1)) (Configuration (n+1)) T):
    cavityNativeFixedRowTaggedField D q T v (cavityNativeFixedRowShift T θ z)=
      cavityNativeFixedRowTaggedField D q T v z+cavityNativeFixedRowParameterChart n θ := by
  exact congrArg Prod.snd (treeNativeFullPointData_coupling_translation (anisotropicUnitCouplings D)
    q (cavityNativeIncidentRow n θ) T (z.1,0) z.2 v)

def cavityNativeFixedRowTaggedLastSquare (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (p : Paper.Overlap) (q : ℕ→Paper.Overlap) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (v : Unit⊕treePathWeightPoint T) :=
  cavityFixedRowNativeLastFieldSquare D μ p  ∘ cavityNativeFixedRowTaggedField D q T v

def cavityNativeFixedRowTaggedRestSquare (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (p : Paper.Overlap) (q : ℕ→Paper.Overlap) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (v : Unit⊕treePathWeightPoint T) :=
  cavityFixedRowNativeRestFieldSquare D μ p  ∘ cavityNativeFixedRowTaggedField D q T v

 theorem measurable_cavityNativeFixedRowTaggedLastSquare (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (p : Paper.Overlap) (q : ℕ→Paper.Overlap) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (v : Unit⊕treePathWeightPoint T) :
    Measurable (cavityNativeFixedRowTaggedLastSquare D μ p q T v) :=
  (boundedJets_cavityFixedRowNativeLastFieldSquare D μ p).1.continuous.measurable.comp
    (measurable_cavityNativeFixedRowTaggedField D q T v)

 theorem measurable_cavityNativeFixedRowTaggedRestSquare (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (p : Paper.Overlap) (q : ℕ→Paper.Overlap) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (v : Unit⊕treePathWeightPoint T) :
    Measurable (cavityNativeFixedRowTaggedRestSquare D μ p q T v) :=
  (boundedJets_cavityFixedRowNativeRestFieldSquare D μ p).1.continuous.measurable.comp
    (measurable_cavityNativeFixedRowTaggedField D q T v)

 theorem cavityFixedRowAffineObservable_jet_bound
    (g : AnisotropicParameter (n+1)→ℝ) (hg : ContDiff ℝ ∞ g)
    (P : AnisotropicParameter (n+1)) (r : ℕ) (B : ℝ)
    (hb : ∀Q,‖iteratedFDeriv ℝ r g Q‖ ≤ B) (θ : Field n) :
    ‖iteratedFDeriv ℝ r (fun y=>g (P+cavityNativeFixedRowParameterChart n y)) θ‖ ≤
      B*‖cavityNativeFixedRowParameterChart n‖^r := by
  let L:=cavityNativeFixedRowParameterChart n
  let f:=fun x:AnisotropicParameter (n+1)=>g (P+x)
  have hf : ContDiff ℝ ∞ f:=hg.comp (contDiff_const.add contDiff_id)
  have he:=L.iteratedFDeriv_comp_right hf θ (by simp : (r:WithTop ℕ∞) ≤ ∞)
  change ‖iteratedFDeriv ℝ r (f ∘ L) θ‖ ≤ _
  rw [he]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [iteratedFDeriv_comp_add_left]
  exact mul_le_mul_of_nonneg_right (hb _) (pow_nonneg (norm_nonneg _) _)

end HexagonPaper
