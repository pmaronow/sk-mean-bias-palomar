module
public import QuantitativeFollowup.VectorQuantileTotalTail

@[expose] public section

/-! Genuine antitonicity and measurability of the actual integrated square
tail, used for the final Lebesgue integral in the cubic moment bound. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem antitone_vectorSelfOverlapSquareTail (hn : 0<n) (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) :
    Antitone (fun θ=>vectorSelfOverlapSquareTail (n:=n) μ β t a ht θ q) :=by
  have hf : Measurable (fun z=>|vectorCenteredSelfOverlap (n:=n) μ β t ht q z|):=
    ((measurable_vectorSelfOverlap μ β t ht q).sub measurable_const).abs
  have hi:=(memLp_vectorCenteredSelfOverlap hn μ β t a ht q).integrable_sq
  intro θ η hθη
  apply integral_mono (hi.indicator (measurableSet_lt (measurable_const (a:=η)) hf))
    (hi.indicator (measurableSet_lt (measurable_const (a:=θ)) hf))
  intro z
  simp only [Set.indicator,mem_setOf_eq]
  split_ifs <;> first | exact le_rfl | positivity | exfalso; linarith

theorem antitone_vectorIntegratedSelfOverlapSquareTail (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (ht : t≤1) :
    Antitone (vectorIntegratedSelfOverlapSquareTail (n:=n) μ s β t ht) :=by
  have hi (θ : ℝ) : IntegrableOn
      (fun v=>vectorSelfOverlapSquareTail (n:=n) μ β t s ht θ (parisiFreeQuantile μ s v)) (Ioo (0:ℝ) (1-s)):=
    Integrable.of_bound
      (((measurable_vectorSelfOverlapSquareTail μ β t s ht θ).comp (parisiFreeQuantile_measurable μ s)).aestronglyMeasurable)
      1 (.of_forall fun v=>by
        rw [Real.norm_of_nonneg (vectorSelfOverlapSquareTail_bounds hn μ β t s ht θ _).1]
        exact (vectorSelfOverlapSquareTail_bounds hn μ β t s ht θ _).2)
  intro θ η hθη
  exact integral_mono (hi η) (hi θ) (fun v=>antitone_vectorSelfOverlapSquareTail hn μ β t s ht _ hθη)

theorem measurable_vectorIntegratedSelfOverlapSquareTail (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (ht : t≤1) :
    Measurable (vectorIntegratedSelfOverlapSquareTail (n:=n) μ s β t ht):=
  (antitone_vectorIntegratedSelfOverlapSquareTail hn μ s β t ht).measurable

theorem vectorIntegratedSelfOverlapSquareTail_bounds (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (ht : t≤1) (θ : ℝ) :
    0≤vectorIntegratedSelfOverlapSquareTail (n:=n) μ s β t ht θ ∧
      vectorIntegratedSelfOverlapSquareTail (n:=n) μ s β t ht θ≤ max (1-s) 0 :=by
  have hi : IntegrableOn
      (fun v=>vectorSelfOverlapSquareTail (n:=n) μ β t s ht θ (parisiFreeQuantile μ s v)) (Ioo (0:ℝ) (1-s)):=
    Integrable.of_bound
      (((measurable_vectorSelfOverlapSquareTail μ β t s ht θ).comp (parisiFreeQuantile_measurable μ s)).aestronglyMeasurable)
      1 (.of_forall fun v=>by
        rw [Real.norm_of_nonneg (vectorSelfOverlapSquareTail_bounds hn μ β t s ht θ _).1]
        exact (vectorSelfOverlapSquareTail_bounds hn μ β t s ht θ _).2)
  refine ⟨integral_nonneg (fun v=>(vectorSelfOverlapSquareTail_bounds hn μ β t s ht θ _).1),?_⟩
  have he:=integral_mono hi (integrable_const (1:ℝ))
    (fun v=>(vectorSelfOverlapSquareTail_bounds hn μ β t s ht θ _).2)
  simpa only [vectorIntegratedSelfOverlapSquareTail,setIntegral_const,smul_eq_mul,mul_one,
    Real.volume_real_Ioo,sub_zero] using he

theorem integrableOn_vectorIntegratedSelfOverlapSquareTail (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (ht : t≤1) (a b : ℝ) :
    IntegrableOn (vectorIntegratedSelfOverlapSquareTail (n:=n) μ s β t ht) (Ioo a b):=
  Integrable.of_bound (measurable_vectorIntegratedSelfOverlapSquareTail hn μ s β t ht).aestronglyMeasurable
    (max (1-s) 0) (.of_forall fun θ=>by
      rw [Real.norm_of_nonneg (vectorIntegratedSelfOverlapSquareTail_bounds hn μ s β t ht θ).1]
      exact (vectorIntegratedSelfOverlapSquareTail_bounds hn μ s β t ht θ).2)

end QuantitativeFollowup
