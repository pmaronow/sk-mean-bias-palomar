module
public import QuantitativeFollowup.SupportingGeneratedIndexedForestCubic

@[expose] public section

/-! The literal absolute three-defect moment of an entire family of
constructed forests uses a single aggregate mark budget. -/
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

theorem supporting_generated_indexed_forests_absolute_three_defects
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (M : I→Measure (CavityGeneratedHistory Paper.Overlap m))
    (W : I→CavityGeneratedConstructedForest m)
    (c : (i : I)→Fin 3→Fin (W i).componentCount)
    (b e : (i : I)→(r : Fin 3)→ObservationLeaf ((W i).tree (c i r)))
    (hsupport : ∀i, ∀ᵐh∂M i, h∈(W i).clockTemplate.orderSet)
    (C : ℝ) (hC : 0≤C)
    (hbudget : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) (∑i : I,M i)
      cavityGeneratedHistoryMarks (ENNReal.ofReal C)) :
    (∑i : I, ∫h,cavityGeneratedForestThreeDefectMoment D μ a
      (W i).depth (W i).tree ((W i).clockTemplate.clock h) (c i) (b i) (e i)∂M i) ≤
      (m : ℝ)*C*cavityThirdMoment D μ a := by
  classical
  let A : Measure (CavityGeneratedHistory Paper.Overlap m) := ∑i : I,M i
  haveI : IsFiniteMeasure A := ⟨hbudget.1.trans_lt ENNReal.ofReal_lt_top⟩
  have hle (i : I) : M i≤A :=
    Finset.single_le_sum (fun j _=>bot_le) (Finset.mem_univ i)
  haveI : ∀i,IsFiniteMeasure (M i) := fun i=>isFiniteMeasure_of_le A (hle i)
  let g : CavityGeneratedHistory Paper.Overlap m→ℝ :=
    fun h=>∑j : Fin m,cavityCubicPairMoment D μ a (h j)
  have hj (η : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure η]
      (j : Fin m) : Integrable (fun h=>cavityCubicPairMoment D μ a (h j)) η := by
    apply (integrable_const (8 : ℝ)).mono'
      ((continuous_cavityCubicPairMoment D μ a).measurable.comp (measurable_pi_apply j)).aestronglyMeasurable
    exact .of_forall fun h=>by
      change ‖cavityCubicPairMoment D μ a (h j)‖≤8
      rw [Real.norm_of_nonneg (cavityCubicPairMoment_bounds D μ a (h j)).1]
      exact (cavityCubicPairMoment_bounds D μ a (h j)).2
  have hg (η : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure η] :
      Integrable g η := integrable_finsetSum _ (fun j _=>hj η j)
  have heach (i : I) :
      (∫h,cavityGeneratedForestThreeDefectMoment D μ a
        (W i).depth (W i).tree ((W i).clockTemplate.clock h) (c i) (b i) (e i)∂M i) ≤
      ∫h,g h∂M i := by
    have hc := continuous_cavityGeneratedForestThreeDefectMoment_family D μ a
      (W i).depth (W i).tree (W i).clockTemplate.clock
      (fun d p _=>(W i).clockTemplate.clock_continuous d p)
      (fun h d p _=>(W i).clockTemplate.clock_step_le h d p) (c i) (b i) (e i)
    have hi : Integrable (fun h=>cavityGeneratedForestThreeDefectMoment D μ a
        (W i).depth (W i).tree ((W i).clockTemplate.clock h) (c i) (b i) (e i)) (M i) := by
      apply (integrable_const (8 : ℝ)).mono' hc.measurable.aestronglyMeasurable
      exact .of_forall fun h=>by
        rw [Real.norm_of_nonneg (cavityGeneratedForestThreeDefectMoment_bounds D μ a
          (W i).depth (W i).tree ((W i).clockTemplate.clock h) (c i) (b i) (e i)).1]
        exact (cavityGeneratedForestThreeDefectMoment_bounds D μ a
          (W i).depth (W i).tree ((W i).clockTemplate.clock h) (c i) (b i) (e i)).2
    apply integral_mono_ae hi (hg (M i))
    exact (hsupport i).mono fun h hh=>
      supporting_generated_constructed_three_defects_le_mark_sum hn D μ a (W i)
        (c i) (b i) (e i) h hh
  have hsum : (∑i : I,∫h,g h∂M i)=∫h,g h∂A := by
    simpa only [A] using (integral_finsetSum_measure (fun i _=>hg (M i))).symm
  apply (Finset.sum_le_sum (fun i _=>heach i)).trans
  rw [hsum,show g=(fun h=>∑j : Fin m,cavityCubicPairMoment D μ a (h j)) from rfl,
    integral_finsetSum _ (fun j _=>hj A j)]
  apply (Finset.sum_le_sum (fun j _=>supporting_generated_coordinate_cubic_of_budget
    D μ a A C hC hbudget j)).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

end QuantitativeFollowup
