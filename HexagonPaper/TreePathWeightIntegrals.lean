module
public import HexagonPaper.TreePathWeightCoalescing
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-! Exact potential integrals on the positive tagged path-tree charges. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace HexagonPaper
open Paper QuantitativePaper FourPapersCommon FiniteTerminalGenealogy
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

private theorem integral_map_measurable_real {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (e : A → B) (he : Measurable e) (F : B → ℝ) (hF : Measurable F)
    (hi : Integrable (fun x => F (e x)) μ) :
    Integrable F (μ.map e) ∧ (∫y,F y ∂μ.map e) = ∫x,F (e x) ∂μ := by
  exact ⟨(integrable_map_measure hF.aestronglyMeasurable he.aemeasurable).mpr hi,
    integral_map_of_stronglyMeasurable he hF.stronglyMeasurable⟩

 theorem treePathInteriorWeight_advance_integral (μ : Paper.ParisiMeasure)
    (q : ℕ → Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (F : Paper.Overlap → ℝ) (G : treePathWeightPoint T → ℝ)
    (hF : Measurable F) (hG : Measurable G)
    (hiF : Integrable F ((μ : Measure Paper.Overlap).restrict (Ioc (q (j+1)) (q j))))
    (hiG : Integrable G (treePathInteriorWeight μ q T)) :
    Integrable (Sum.elim F G) (treePathInteriorWeight μ q (.advance T)) ∧
    (∫z,Sum.elim F G z ∂treePathInteriorWeight μ q (.advance T)) =
      (∫r in Ioc (q (j+1)) (q j),F r ∂(μ : Measure Paper.Overlap))+
      ∫z,G z ∂treePathInteriorWeight μ q T := by
  have hm : Measurable (Sum.elim F G) := hF.sumElim hG
  have hL := integral_map_measurable_real
    ((μ : Measure Paper.Overlap).restrict (Ioc (q (j+1)) (q j))) Sum.inl measurable_inl
    (Sum.elim F G) hm hiF
  have hR := integral_map_measurable_real (treePathInteriorWeight μ q T) Sum.inr measurable_inr
    (Sum.elim F G) hm hiG
  refine ⟨hL.1.add_measure hR.1,?_⟩
  change (∫z,Sum.elim F G z ∂(_+_)) = _
  rw [integral_add_measure hL.1 hR.1,hL.2,hR.2]
  simp only [Sum.elim_inl,Sum.elim_inr]

 theorem treePathInteriorWeight_fork_integral (μ : Paper.ParisiMeasure)
    (q : ℕ → Paper.Overlap) {j : ℕ} (T U : FiniteTerminalGenealogy j)
    (v : ℝ) (F : treePathWeightPoint T → ℝ) (G : treePathWeightPoint U → ℝ)
    (hF : Measurable F) (hG : Measurable G)
    (hiF : Integrable F (treePathInteriorWeight μ q T))
    (hiG : Integrable G (treePathInteriorWeight μ q U)) :
    let H := Sum.elim (fun _ : Unit => v) (Sum.elim F G)
    Integrable H (treePathInteriorWeight μ q (.fork T U)) ∧
    (∫z,H z ∂treePathInteriorWeight μ q (.fork T U)) =
      Paper.parisiCDF μ (q j)*v+(∫z,F z ∂treePathInteriorWeight μ q T)+
        ∫z,G z ∂treePathInteriorWeight μ q U := by
  dsimp only
  let H := Sum.elim (fun _ : Unit => v) (Sum.elim F G)
  have hm : Measurable H := measurable_const.sumElim (hF.sumElim hG)
  have hL := integral_map_measurable_real (treePathInteriorWeight μ q T)
    (Sum.inr ∘ Sum.inl) (measurable_inr.comp measurable_inl) H hm hiF
  have hR := integral_map_measurable_real (treePathInteriorWeight μ q U)
    (Sum.inr ∘ Sum.inr) (measurable_inr.comp measurable_inr) H hm hiG
  have hZ : Integrable H ((Paper.parisiCDF μ (q j)).toNNReal • Measure.dirac (Sum.inl ())) :=
    (integrable_dirac' hm.stronglyMeasurable (by finiteness)).smul_measure_nnreal
  refine ⟨(hZ.add_measure hL.1).add_measure hR.1,?_⟩
  change (∫z,H z ∂(_+_+_)) = _
  rw [integral_add_measure (hZ.add_measure hL.1) hR.1,
    integral_add_measure hZ hL.1,hL.2,hR.2,
    integral_smul_nnreal_measure,integral_dirac' _ _ hm.stronglyMeasurable]
  simp only [H,Function.comp_def,Sum.elim_inl,Sum.elim_inr,NNReal.smul_def,smul_eq_mul,
    Real.coe_toNNReal _ (Paper.parisiCDF_nonneg μ _)]

 theorem treePathWeight_root_integral (μ : Paper.ParisiMeasure) (a : ℝ)
    (hμ : μ ∈ scalarFloor a) (q : ℕ → Paper.Overlap) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (v : ℝ) (F : treePathWeightPoint T → ℝ)
    (hF : Measurable F) (hiF : Integrable F (treePathInteriorWeight μ q T)) :
    let H := Sum.elim (fun _ : Unit => v) F
    Integrable H (treePathWeight μ a q T) ∧
    (∫z,H z ∂treePathWeight μ a q T) =
      (Paper.parisiCDF μ (q j)-a)*v+∫z,F z ∂treePathInteriorWeight μ q T := by
  dsimp only
  let H := Sum.elim (fun _ : Unit => v) F
  have hm : Measurable H := measurable_const.sumElim hF
  have hR := integral_map_measurable_real (treePathInteriorWeight μ q T)
    Sum.inr measurable_inr H hm hiF
  have hZ : Integrable H ((Paper.parisiCDF μ (q j)-a).toNNReal • Measure.dirac (Sum.inl ())) :=
    (integrable_dirac' hm.stronglyMeasurable (by finiteness)).smul_measure_nnreal
  have hroot : 0≤Paper.parisiCDF μ (q j)-a :=
    sub_nonneg.mpr (scalarFloor_cdf_lower hμ (q j).property.1)
  refine ⟨hZ.add_measure hR.1,?_⟩
  change (∫z,H z ∂(_+_)) = _
  rw [integral_add_measure hZ hR.1,hR.2,
    integral_smul_nnreal_measure,integral_dirac' _ _ hm.stronglyMeasurable]
  simp only [H,Sum.elim_inl,Sum.elim_inr,NNReal.smul_def,smul_eq_mul,Real.coe_toNNReal _ hroot]

end HexagonPaper
