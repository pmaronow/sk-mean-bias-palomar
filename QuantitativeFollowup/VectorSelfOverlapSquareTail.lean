module
public import QuantitativeFollowup.VectorSelfOverlapMoments

@[expose] public section

/-! Actual two-sided square tails of the marked self-overlap, with genuine
measurability, integrability and the decomposition into the two tails. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorSelfOverlapSquareTail (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1)
    (θ : ℝ) (q : Paper.Overlap) : ℝ :=
  ∫z,{z | θ < |vectorCenteredSelfOverlap (n:=n) μ β t ht q z| }.indicator
    (fun z=>vectorCenteredSelfOverlap μ β t ht q z^2) z ∂vectorMeasureSpinPathLaw μ β t a ht

def vectorSelfOverlapUpperSquareTail (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1)
    (θ : ℝ) (q : Paper.Overlap) : ℝ :=
  ∫z,{z | θ<vectorCenteredSelfOverlap (n:=n) μ β t ht q z}.indicator
    (fun z=>vectorCenteredSelfOverlap μ β t ht q z^2) z ∂vectorMeasureSpinPathLaw μ β t a ht

def vectorSelfOverlapLowerSquareTail (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1)
    (θ : ℝ) (q : Paper.Overlap) : ℝ :=
  ∫z,{z | vectorCenteredSelfOverlap (n:=n) μ β t ht q z< -θ}.indicator
    (fun z=>vectorCenteredSelfOverlap μ β t ht q z^2) z ∂vectorMeasureSpinPathLaw μ β t a ht

theorem measurable_vectorSelfOverlapUpperSquareTail (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (θ : ℝ) :
    Measurable (vectorSelfOverlapUpperSquareTail (n:=n) μ β t a ht θ) := by
  let :=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  have hf:=measurable_uncurry_vectorCenteredSelfOverlap (n:=n) μ β t ht
  have hF : Measurable (Function.uncurry fun q z=>{z | θ<vectorCenteredSelfOverlap (n:=n) μ β t ht q z}.indicator
      (fun z=>vectorCenteredSelfOverlap μ β t ht q z^2) z) :=by
    convert (hf.pow_const 2).indicator (measurableSet_lt (measurable_const (a:=θ)) hf) using 1
    funext p
    simp only [Function.uncurry,Set.indicator,mem_setOf_eq]
  exact hF.stronglyMeasurable.integral_prod_right.measurable

theorem measurable_vectorSelfOverlapLowerSquareTail (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (θ : ℝ) :
    Measurable (vectorSelfOverlapLowerSquareTail (n:=n) μ β t a ht θ) := by
  let :=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  have hf:=measurable_uncurry_vectorCenteredSelfOverlap (n:=n) μ β t ht
  have hF : Measurable (Function.uncurry fun q z=>{z | vectorCenteredSelfOverlap (n:=n) μ β t ht q z< -θ}.indicator
      (fun z=>vectorCenteredSelfOverlap μ β t ht q z^2) z) :=by
    convert (hf.pow_const 2).indicator (measurableSet_lt hf (measurable_const (a:=-θ))) using 1
    funext p
    simp only [Function.uncurry,Set.indicator,mem_setOf_eq]
  exact hF.stronglyMeasurable.integral_prod_right.measurable

theorem measurable_vectorSelfOverlapSquareTail (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (θ : ℝ) :
    Measurable (vectorSelfOverlapSquareTail (n:=n) μ β t a ht θ) := by
  let :=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  have hf:=measurable_uncurry_vectorCenteredSelfOverlap (n:=n) μ β t ht
  have hF : Measurable (Function.uncurry fun q z=>{z | θ < |vectorCenteredSelfOverlap (n:=n) μ β t ht q z| }.indicator
      (fun z=>vectorCenteredSelfOverlap μ β t ht q z^2) z) :=by
    convert (hf.pow_const 2).indicator (measurableSet_lt (measurable_const (a:=θ)) hf.abs) using 1
    funext p
    simp only [Function.uncurry,Set.indicator,mem_setOf_eq]
  exact hF.stronglyMeasurable.integral_prod_right.measurable

theorem vectorSelfOverlap_one_sided_square_tail_bounds (hn : 0<n) (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (θ : ℝ) (q : Paper.Overlap) :
    (0≤vectorSelfOverlapUpperSquareTail (n:=n) μ β t a ht θ q ∧
      vectorSelfOverlapUpperSquareTail (n:=n) μ β t a ht θ q≤1) ∧
    (0≤vectorSelfOverlapLowerSquareTail (n:=n) μ β t a ht θ q ∧
      vectorSelfOverlapLowerSquareTail (n:=n) μ β t a ht θ q≤1) := by
  let :=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  have hf : Measurable (vectorCenteredSelfOverlap (n:=n) μ β t ht q):=
    (measurable_vectorSelfOverlap μ β t ht q).sub measurable_const
  have hi:=(memLp_vectorCenteredSelfOverlap hn μ β t a ht q).integrable_sq
  have hu:=integral_mono (hi.indicator (measurableSet_lt (measurable_const (a:=θ)) hf)) hi
    (fun z=>by simp only [Set.indicator,mem_setOf_eq];split_ifs <;> first | exact le_rfl | positivity)
  have hl:=integral_mono (hi.indicator (measurableSet_lt hf (measurable_const (a:=-θ)))) hi
    (fun z=>by simp only [Set.indicator,mem_setOf_eq];split_ifs <;> first | exact le_rfl | positivity)
  have hb:=(vectorCenteredSelfOverlapSecond_bounds hn μ β t a ht q).2
  exact ⟨⟨integral_nonneg (fun z=>Set.indicator_nonneg (fun _ _=>sq_nonneg _) _),hu.trans hb⟩,
    ⟨integral_nonneg (fun z=>Set.indicator_nonneg (fun _ _=>sq_nonneg _) _),hl.trans hb⟩⟩

theorem vectorSelfOverlapSquareTail_eq_sum (hn : 0<n) (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (θ : ℝ) (hθ : 0≤θ) (q : Paper.Overlap) :
    vectorSelfOverlapSquareTail (n:=n) μ β t a ht θ q=
      vectorSelfOverlapUpperSquareTail (n:=n) μ β t a ht θ q+
      vectorSelfOverlapLowerSquareTail (n:=n) μ β t a ht θ q := by
  have hf : Measurable (vectorCenteredSelfOverlap (n:=n) μ β t ht q):=
    (measurable_vectorSelfOverlap μ β t ht q).sub measurable_const
  have hi:=(memLp_vectorCenteredSelfOverlap hn μ β t a ht q).integrable_sq
  unfold vectorSelfOverlapSquareTail vectorSelfOverlapUpperSquareTail vectorSelfOverlapLowerSquareTail
  rw [←integral_add (hi.indicator (measurableSet_lt (measurable_const (a:=θ)) hf))
    (hi.indicator (measurableSet_lt hf (measurable_const (a:=-θ))))]
  apply integral_congr_ae
  exact .of_forall fun z=>by
    dsimp only [Pi.add_apply]
    have he : θ < |vectorCenteredSelfOverlap μ β t ht q z| ↔
        θ<vectorCenteredSelfOverlap μ β t ht q z ∨ vectorCenteredSelfOverlap μ β t ht q z< -θ :=by
      rw [lt_abs]
      constructor <;> intro h <;> rcases h with h|h
      · exact Or.inl h
      · exact Or.inr (by linarith)
      · exact Or.inl h
      · exact Or.inr (by linarith)
    by_cases hp : θ<vectorCenteredSelfOverlap μ β t ht q z
    · have hm : ¬vectorCenteredSelfOverlap μ β t ht q z< -θ :=by intro h;linarith
      simp only [Set.indicator,mem_setOf_eq,he,hp,hm,true_or,if_true,if_false,add_zero]
    · by_cases hm : vectorCenteredSelfOverlap μ β t ht q z< -θ
      · simp only [Set.indicator,mem_setOf_eq,he,hp,hm,false_or,if_true,if_false,zero_add]
      · simp only [Set.indicator,mem_setOf_eq,he,hp,hm,false_or,if_false,add_zero]

theorem vectorSelfOverlapSquareTail_bounds (hn : 0<n) (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (θ : ℝ) (q : Paper.Overlap) :
    0≤vectorSelfOverlapSquareTail (n:=n) μ β t a ht θ q ∧
      vectorSelfOverlapSquareTail (n:=n) μ β t a ht θ q≤1 := by
  let :=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  have hf : Measurable (fun z=>|vectorCenteredSelfOverlap (n:=n) μ β t ht q z|):=
    ((measurable_vectorSelfOverlap μ β t ht q).sub measurable_const).abs
  have hi:=(memLp_vectorCenteredSelfOverlap hn μ β t a ht q).integrable_sq
  have hu:=integral_mono (hi.indicator (measurableSet_lt (measurable_const (a:=θ)) hf)) hi
    (fun z=>by simp only [Set.indicator,mem_setOf_eq];split_ifs <;> first | exact le_rfl | positivity)
  exact ⟨integral_nonneg (fun z=>Set.indicator_nonneg (fun _ _=>sq_nonneg _) _),
    hu.trans (vectorCenteredSelfOverlapSecond_bounds hn μ β t a ht q).2⟩

end QuantitativeFollowup
