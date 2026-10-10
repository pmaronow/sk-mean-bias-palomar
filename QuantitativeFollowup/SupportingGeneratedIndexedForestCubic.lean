module
public import QuantitativeFollowup.FollowupCavityGeneratedForestHistoryPrefactor

@[expose] public section

/-! A family of genuine source charts uses one aggregate mark budget.
The estimate has no factor for the number of charts or grid cells.
Concrete generation supplies the actual budget and order support. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ} {I : Type*} [Fintype I]

theorem supporting_generated_coordinate_cubic_of_budget
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (C : ℝ) (hC : 0≤C)
    (hM : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) M
      cavityGeneratedHistoryMarks (ENNReal.ofReal C)) (i : Fin m) :
    (∫h, cavityCubicPairMoment D μ a (h i) ∂M) ≤ C*cavityThirdMoment D μ a := by
  have hi := (integrable_cavityCubicPairMoment D μ a).smul_measure (c:=ENNReal.ofReal C) ENNReal.ofReal_ne_top
  have hh := integral_mono_measure (hM.2 i)
    (.of_forall fun q => (cavityCubicPairMoment_bounds D μ a q).1) hi
  rw [integral_smul_measure] at hh
  rw [integral_map (μ:=M) (φ:=cavityGeneratedHistoryMarks i)
    (f:=cavityCubicPairMoment D μ a) (cavityGeneratedHistoryMarks_measurable i).aemeasurable
    (continuous_cavityCubicPairMoment D μ a).measurable.aestronglyMeasurable] at hh
  simpa only [cavityGeneratedHistoryMarks, ENNReal.toReal_ofReal hC,
    smul_eq_mul, cavityThirdMoment] using hh

theorem supporting_generated_constructed_three_defects_le_mark_sum
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin 3→Fin W.componentCount)
    (b e : (r : Fin 3)→ObservationLeaf (W.tree (c r)))
    (h : CavityGeneratedHistory Paper.Overlap m) (hh : h∈W.clockTemplate.orderSet) :
    cavityGeneratedForestThreeDefectMoment D μ a W.depth W.tree (W.clockTemplate.clock h) c b e ≤
      ∑i : Fin m, cavityCubicPairMoment D μ a (h i) := by
  classical
  by_cases hbe : ∀r, b r≠e r
  · have hb (r : Fin 3) : cavityCubicPairMoment D μ a
        (W.clockTemplate.clock h (c r) (observationCommonLevel (W.tree (c r)) (b r) (e r))) ≤
          ∑i : Fin m, cavityCubicPairMoment D μ a (h i) := by
      obtain ⟨i,hi⟩ := W.clockTemplate.branch_clock_is_mark h hh (c r) (b r) (e r) (hbe r)
      calc
        _ = cavityCubicPairMoment D μ a (h i) := congrArg (cavityCubicPairMoment D μ a) hi
        _ ≤ _ := Finset.single_le_sum (fun j _ => (cavityCubicPairMoment_bounds D μ a (h j)).1)
          (Finset.mem_univ i)
    exact (cavityGeneratedForestThreeDefectMoment_le D μ a W.depth W.tree
      (W.clockTemplate.clock h) (W.clockTemplate.clock_terminal h)
      (W.clockTemplate.clock_initial h) (fun i p _=>W.clockTemplate.clock_step_le h i p)
      c b e hbe).trans (by linarith [hb 0,hb 1,hb 2])
  · push_neg at hbe
    obtain ⟨r,hr⟩ := hbe
    rw [cavityGeneratedForestThreeDefectMoment_eq_zero_of_same hn D μ a W.depth W.tree
      (W.clockTemplate.clock h) (W.clockTemplate.clock_terminal h) c b e r hr]
    exact Finset.sum_nonneg (fun i _ => (cavityCubicPairMoment_bounds D μ a (h i)).1)

theorem supporting_generated_indexed_forests_prefactor_three_defects
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (M : I→Measure (CavityGeneratedHistory Paper.Overlap m))
    (W : I→CavityGeneratedConstructedForest m)
    (c : (i : I)→Fin 3→Fin (W i).componentCount)
    (b e : (i : I)→(r : Fin 3)→ObservationLeaf ((W i).tree (c i r)))
    (F : (i : I)→CavityGeneratedHistory Paper.Overlap m→
      CavityGeneratedForestTerminalSample (n:=n) (W i).depth (W i).tree→ℝ)
    (hcts : ∀i σ, Continuous (fun h=>F i h σ)) (hF : ∀i h σ, |F i h σ|≤1)
    (hsupport : ∀i, ∀ᵐh∂M i, h∈(W i).clockTemplate.orderSet)
    (C : ℝ) (hC : 0≤C)
    (hbudget : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) (∑i : I,M i)
      cavityGeneratedHistoryMarks (ENNReal.ofReal C)) :
    (∑i : I, ∫h, |cavityGeneratedForestHistoryPrefactorExpectation D μ a
      (W i).depth (W i).tree (W i).clockTemplate.clock (c i) (b i) (e i) (F i) h| ∂M i) ≤
      (m : ℝ)*C*cavityThirdMoment D μ a := by
  classical
  let A : Measure (CavityGeneratedHistory Paper.Overlap m) := ∑i : I,M i
  haveI : IsFiniteMeasure A := ⟨hbudget.1.trans_lt ENNReal.ofReal_lt_top⟩
  have hle (i : I) : M i≤A :=
    Finset.single_le_sum (fun j _ => bot_le) (Finset.mem_univ i)
  haveI : ∀i, IsFiniteMeasure (M i) := fun i => isFiniteMeasure_of_le A (hle i)
  let g : CavityGeneratedHistory Paper.Overlap m→ℝ :=
    fun h=>∑j : Fin m, cavityCubicPairMoment D μ a (h j)
  have hj (η : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure η]
      (j : Fin m) : Integrable (fun h=>cavityCubicPairMoment D μ a (h j)) η := by
    apply (integrable_const (8 : ℝ)).mono'
      ((continuous_cavityCubicPairMoment D μ a).measurable.comp (measurable_pi_apply j)).aestronglyMeasurable
    exact .of_forall fun h=>by
      change ‖cavityCubicPairMoment D μ a (h j)‖ ≤ 8
      rw [Real.norm_of_nonneg (cavityCubicPairMoment_bounds D μ a (h j)).1]
      exact (cavityCubicPairMoment_bounds D μ a (h j)).2
  have hg (η : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure η] :
      Integrable g η := integrable_finsetSum _ (fun j _=>hj η j)
  have heach (i : I) :
      (∫h, |cavityGeneratedForestHistoryPrefactorExpectation D μ a
        (W i).depth (W i).tree (W i).clockTemplate.clock (c i) (b i) (e i) (F i) h| ∂M i) ≤ ∫h,g h∂M i := by
    have hc := continuous_cavityGeneratedForestHistoryPrefactorExpectation (n:=n) D μ a
      (W i).depth (W i).tree (W i).clockTemplate.clock
      (fun d p _=>(W i).clockTemplate.clock_continuous d p)
      (fun h d p _=>(W i).clockTemplate.clock_step_le h d p) (c i) (b i) (e i) (F i) (hcts i)
    have hi : Integrable (fun h=>|cavityGeneratedForestHistoryPrefactorExpectation D μ a
        (W i).depth (W i).tree (W i).clockTemplate.clock (c i) (b i) (e i) (F i) h|) (M i) := by
      apply (integrable_const (8 : ℝ)).mono' hc.abs.measurable.aestronglyMeasurable
      exact .of_forall fun h=>by
        rw [Real.norm_of_nonneg (abs_nonneg _)]
        have hb := norm_cavityGeneratedForestHistoryPrefactorExpectation_le D μ a
          (W i).depth (W i).tree (W i).clockTemplate.clock (c i) (b i) (e i) (F i) (hF i) h
        rw [Real.norm_eq_abs] at hb
        exact hb.trans (cavityGeneratedForestThreeDefectMoment_bounds D μ a (W i).depth
          (W i).tree ((W i).clockTemplate.clock h) (c i) (b i) (e i)).2
    apply integral_mono_ae hi (hg (M i))
    filter_upwards [hsupport i] with h hh
    have hb := norm_cavityGeneratedForestHistoryPrefactorExpectation_le D μ a
      (W i).depth (W i).tree (W i).clockTemplate.clock (c i) (b i) (e i) (F i) (hF i) h
    rw [Real.norm_eq_abs] at hb
    exact hb.trans (supporting_generated_constructed_three_defects_le_mark_sum hn D μ a (W i)
      (c i) (b i) (e i) h hh)
  have hsum : (∑i : I, ∫h,g h∂M i) = ∫h,g h∂A := by
    simpa only [A] using (integral_finsetSum_measure (fun i _=>hg (M i))).symm
  apply (Finset.sum_le_sum (fun i _=>heach i)).trans
  rw [hsum, show g = (fun h=>∑j : Fin m,cavityCubicPairMoment D μ a (h j)) from rfl,
    integral_finsetSum _ (fun j _=>hj A j)]
  apply (Finset.sum_le_sum (fun j _=>supporting_generated_coordinate_cubic_of_budget
    D μ a A C hC hbudget j)).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

end QuantitativeFollowup
