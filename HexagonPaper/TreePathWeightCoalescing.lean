module
public import FourPapersCommon.FiniteCascadeTreeRecords
public import QuantitativePaper.ScalarFloorContinuity
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

/-! Positive full-path genealogy charges with exact total mass.
Edge charges use the actual profile on (parent,child], including atoms
at the upper endpoint. Branch charges and the excess root atom are
nonnegative measures on a tagged vertex/edge coproduct. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace HexagonPaper
open Paper QuantitativePaper FourPapersCommon FiniteTerminalGenealogy
set_option maxHeartbeats 100000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

@[reducible] def treePathWeightPoint : {j : ℕ} → FiniteTerminalGenealogy j → Type
  | _, .leaf => Unit
  | _, .advance T => Paper.Overlap ⊕ treePathWeightPoint T
  | _, .fork T U => Unit ⊕ (treePathWeightPoint T ⊕ treePathWeightPoint U)

@[reducible] def treePathWeightMeasurableSpace : {j : ℕ} →
    (T : FiniteTerminalGenealogy j) → MeasurableSpace (treePathWeightPoint T)
  | _, .leaf => inferInstanceAs (MeasurableSpace Unit)
  | _, .advance T => @Sum.instMeasurableSpace _ _ inferInstance (treePathWeightMeasurableSpace T)
  | _, .fork T U => @Sum.instMeasurableSpace _ _ inferInstance
      (@Sum.instMeasurableSpace _ _ (treePathWeightMeasurableSpace T) (treePathWeightMeasurableSpace U))

instance {j : ℕ} (T : FiniteTerminalGenealogy j) : MeasurableSpace (treePathWeightPoint T) :=
  treePathWeightMeasurableSpace T

@[reducible] def treePathInteriorWeight (μ : Paper.ParisiMeasure) (q : ℕ → Paper.Overlap) :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) → Measure (treePathWeightPoint T)
  | _, .leaf => 0
  | _, @FiniteTerminalGenealogy.advance j T =>
      ((μ : Measure Paper.Overlap).restrict (Ioc (q (j+1)) (q j))).map Sum.inl +
        (treePathInteriorWeight μ q T).map Sum.inr
  | j, .fork T U =>
      (Paper.parisiCDF μ (q j)).toNNReal • Measure.dirac (Sum.inl ()) +
        (treePathInteriorWeight μ q T).map (Sum.inr ∘ Sum.inl) +
        (treePathInteriorWeight μ q U).map (Sum.inr ∘ Sum.inr)

 theorem isFiniteMeasure_treePathInteriorWeight (μ : Paper.ParisiMeasure)
    (q : ℕ → Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j) :
    IsFiniteMeasure (treePathInteriorWeight μ q T) := by
  induction T with
  | leaf => change IsFiniteMeasure (0 : Measure Unit); infer_instance
  | advance T ih =>
      haveI := ih
      change IsFiniteMeasure (_ + _)
      infer_instance
  | fork T U ihT ihU =>
      haveI := ihT
      haveI := ihU
      change IsFiniteMeasure (_ + _ + _)
      infer_instance

attribute [local instance] isFiniteMeasure_treePathInteriorWeight

 theorem overlap_Iic_measureReal_eq_cdf (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    (μ : Measure Paper.Overlap).real (Iic q) = Paper.parisiCDF μ q := rfl

 theorem overlap_Ioc_measureReal_eq_cdf_sub (μ : Paper.ParisiMeasure)
    (q h : Paper.Overlap) (hqh : q ≤ h) :
    ((μ : Measure Paper.Overlap).restrict (Ioc q h)).real univ =
      Paper.parisiCDF μ h-Paper.parisiCDF μ q := by
  rw [measureReal_restrict_apply_univ]
  have he : Iic h \ Iic q = Ioc q h := by
    ext r
    simp only [mem_sdiff,mem_Iic,mem_Ioc,not_le]
    tauto
  rw [←he,measureReal_sdiff (Iic_subset_Iic.mpr hqh) measurableSet_Iic,
    overlap_Iic_measureReal_eq_cdf,overlap_Iic_measureReal_eq_cdf]

 theorem treePathWeight_scalarDirac_mass {Z : Type} [MeasurableSpace Z]
    (r : ℝ) (hr : 0≤r) (z : Z) :
    (r.toNNReal • Measure.dirac z).real univ = r := by
  rw [measureReal_nnreal_smul_apply,Real.coe_toNNReal _ hr]
  simp [Measure.real]

 theorem treePathInteriorWeight_mass (μ : Paper.ParisiMeasure)
    (q : ℕ → Paper.Overlap) (h0 : q 0=1) (hq : ∀j,q (j+1)≤q j)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    Paper.parisiCDF μ (q j)+(treePathInteriorWeight μ q T).real univ =
      (FiniteCascadeGenealogy.leafCount T.asGenealogy : ℝ) := by
  induction T with
  | leaf =>
      simp only [treePathInteriorWeight,measureReal_zero_apply,add_zero,asGenealogy,
        FiniteCascadeGenealogy.leafCount,Nat.cast_one,h0]
      exact Paper.parisiCDF_eq_one_of_one_le μ le_rfl
  | @advance j T ih =>
      haveI := isFiniteMeasure_treePathInteriorWeight μ q T
      change Paper.parisiCDF μ (q (j+1))+
        (((μ : Measure Paper.Overlap).restrict (Ioc (q (j+1)) (q j))).map Sum.inl +
          (treePathInteriorWeight μ q T).map Sum.inr).real univ = _
      rw [measureReal_add_apply,
        map_measureReal_apply measurable_inl MeasurableSet.univ,
        map_measureReal_apply measurable_inr MeasurableSet.univ]
      simp only [preimage_univ]
      rw [overlap_Ioc_measureReal_eq_cdf_sub μ _ _ (hq j)]
      simpa only [asGenealogy,FiniteCascadeGenealogy.leafCount] using
        (show Paper.parisiCDF μ (q (j+1))+
          (Paper.parisiCDF μ (q j)-Paper.parisiCDF μ (q (j+1))+
            (treePathInteriorWeight μ q T).real univ)=
            (FiniteCascadeGenealogy.leafCount T.asGenealogy : ℝ) by linarith [ih])
  | @fork j T U ihT ihU =>
      haveI := isFiniteMeasure_treePathInteriorWeight μ q T
      haveI := isFiniteMeasure_treePathInteriorWeight μ q U
      change Paper.parisiCDF μ (q j)+
        (((Paper.parisiCDF μ (q j)).toNNReal • Measure.dirac (Sum.inl ()) +
          (treePathInteriorWeight μ q T).map (Sum.inr ∘ Sum.inl) +
          (treePathInteriorWeight μ q U).map (Sum.inr ∘ Sum.inr)).real univ) = _
      rw [measureReal_add_apply,measureReal_add_apply,
        map_measureReal_apply (measurable_inr.comp measurable_inl) MeasurableSet.univ,
        map_measureReal_apply (measurable_inr.comp measurable_inr) MeasurableSet.univ]
      simp only [preimage_univ]
      rw [treePathWeight_scalarDirac_mass _ (Paper.parisiCDF_nonneg μ _) (Sum.inl ())]
      simp only [asGenealogy,FiniteCascadeGenealogy.leafCount,Nat.cast_add]
      linarith [ihT,ihU]

 def treePathWeight (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) : Measure (Unit ⊕ treePathWeightPoint T) :=
    (Paper.parisiCDF μ (q j)-a).toNNReal • Measure.dirac (Sum.inl ()) +
      (treePathInteriorWeight μ q T).map Sum.inr

 theorem isFiniteMeasure_treePathWeight (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) {j : ℕ} (T : FiniteTerminalGenealogy j) :
    IsFiniteMeasure (treePathWeight μ a q T) := by
  haveI := isFiniteMeasure_treePathInteriorWeight μ q T
  unfold treePathWeight
  infer_instance

 theorem treePathWeight_mass (μ : Paper.ParisiMeasure) (a : ℝ) (hμ : μ ∈ scalarFloor a)
    (q : ℕ → Paper.Overlap) (h0 : q 0=1) (hq : ∀j,q (j+1)≤q j)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    (treePathWeight μ a q T).real univ =
      (FiniteCascadeGenealogy.leafCount T.asGenealogy : ℝ)-a := by
  haveI := isFiniteMeasure_treePathInteriorWeight μ q T
  have hroot : 0 ≤ Paper.parisiCDF μ (q j)-a :=
    sub_nonneg.mpr (scalarFloor_cdf_lower hμ (q j).property.1)
  unfold treePathWeight
  rw [measureReal_add_apply,
    map_measureReal_apply measurable_inr MeasurableSet.univ]
  simp only [preimage_univ]
  rw [treePathWeight_scalarDirac_mass _ hroot (Sum.inl ())]
  have hh := treePathInteriorWeight_mass μ q h0 hq T
  change Paper.parisiCDF μ (q j)-a+(treePathInteriorWeight μ q T).real univ = _
  linarith

end HexagonPaper
