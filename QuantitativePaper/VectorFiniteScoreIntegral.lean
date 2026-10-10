module
public import QuantitativePaper.VectorScoreHistoryTransport

@[expose] public section

/-! The actual finite-grid weighted score is exactly its posterior history
observable.  Pushforward of the free measure retains partial root atoms. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon
open scoped NNReal BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def vectorFiniteOverlapScore (s : RSBScheme k) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (p : VectorDisorderBrownianSample n×Configuration n) : ℝ :=
  normalizedSpinScore (vectorFiniteTailGradient s β t q p.1.1
    (vectorFiniteState s β t ht (q : ℝ).toNNReal p.1)) p.2

theorem measurable_vectorFiniteOverlapScore_level (s : RSBScheme k) (β t : ℝ)
    (ht : t≤1) (p : VectorDisorderBrownianSample n×Configuration n) :
    Measurable (fun q : Paper.Overlap=>vectorFiniteOverlapScore s β t ht q p) := by
  have hc : Measurable (fun q : Paper.Overlap=>(q : ℝ).toNNReal) :=
    continuous_real_toNNReal.measurable.comp measurable_subtype_coe
  have hX : Measurable (fun q : Paper.Overlap=>
      vectorFiniteState s β t ht (q : ℝ).toNNReal p.1) := by
    have hh:=(measurable_uncurry_vectorFiniteState (n:=n) s β t ht).comp
      (hc.prodMk (measurable_const (a:=p.1)))
    exact hh
  have hz : Measurable (fun q : Paper.Overlap=>
      (q,(p.1.1,vectorFiniteState s β t ht (q : ℝ).toNNReal p.1))) :=
    measurable_id.prodMk (measurable_const.prodMk hX)
  have hh:=(measurable_vectorFiniteTailGradient (n:=n) s β t).comp hz
  exact (continuous_normalizedSpinScore p.2).measurable.comp hh

theorem vectorHistoryWeightedScore_finite_eq_freeIntegral (s : RSBScheme k)
    (β t a : ℝ) (ht : t≤1) (ha0 : 0≤a) (ha : a ≤ s.m 1) (hq : s.q 1=0)
    (κ : Paper.Overlap→ℝ) (p : VectorDisorderBrownianSample n×Configuration n) :
    vectorHistoryWeightedScore s β t a κ (vectorFiniteHistory s β t ht (k+2) p.1,p.2)=
      ∫q,κ q*vectorFiniteOverlapScore s β t ht q p
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a := by
  rw [←vectorProfileFreeMeasure_eq_actual_free s a ha0 ha hq,
    integral_vectorProfileFreeMeasure s a ha]
  unfold vectorHistoryWeightedScore
  apply Finset.sum_congr rfl
  intro i _
  have hi : vectorPosteriorFeatureTime i≤k+2 := by
    cases i <;> dsimp [vectorPosteriorFeatureTime] <;> omega
  rw [vectorHistoryScore_finite s β t ht _ hi]
  exact mul_assoc _ _ _

theorem vectorDyadicWeightedOverlapScore_eq_history (μ : Paper.ParisiMeasure)
    (a β t : ℝ) (ht : t≤1) (ha : a∈Icc (0 : ℝ) 1) (hμ : μ∈scalarFloor a)
    (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (j : ℕ)
    (p : VectorDisorderBrownianSample n×Configuration n) :
    vectorDyadicWeightedOverlapScore μ a β t ht κ j p=
      vectorHistoryWeightedScore (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a κ
        (vectorFiniteHistory (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t ht
          (vectorDyadicIndex j+3) p.1,p.2) := by
  let s:=Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  have hs : a ≤ s.m 1 := parisiGridRSBScheme_floor μ a hμ _
  have hq : s.q 1=0 := Paper.parisiGridSchemeOverlap_one _
  rw [vectorHistoryWeightedScore_finite_eq_freeIntegral s β t a ht ha.1 hs hq]
  rw [FRSB.parisiSchemeMeasure_grid_eq]
  have hm : Measurable (fun q : Paper.Overlap=>κ q*vectorFiniteOverlapScore s β t ht q p) :=
    hκ.mul (measurable_vectorFiniteOverlapScore_level s β t ht p)
  rw [integral_parisiFreeMeasure_grid μ a ha hμ (vectorDyadicIndex j)
    (fun q=>κ q*vectorFiniteOverlapScore s β t ht q p) hm]
  unfold vectorDyadicWeightedOverlapScore
  apply integral_congr_ae
  exact .of_forall fun q=>by
    rfl

theorem variance_vectorDyadicWeightedOverlapScore_eq_posterior (μ : Paper.ParisiMeasure)
    (a β t : ℝ) (hβ : β≠0) (ht : t<1) (ha : a∈Icc (0 : ℝ) 1)
    (hμ : μ∈scalarFloor a) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (j : ℕ) :
    variance (vectorDyadicWeightedOverlapScore (n:=n) μ a β t ht.le κ j)
      (vectorFiniteSpinPathLaw (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a ht.le)=
    variance (fun p : VectorGaussianSpace n (vectorDyadicIndex j+1)×Configuration n=>
      vectorEuclideanWeightedOverlapScore (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
        β t a (fun q=>κ (projIcc (0 : ℝ) 1 zero_le_one q)) p.2 p.1)
      (vectorEuclideanJointLaw (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a) := by
  have he := funext fun p : VectorDisorderBrownianSample n×Configuration n=>vectorDyadicWeightedOverlapScore_eq_history μ a β t ht.le ha hμ κ hκ j p
  rw [he]
  exact variance_vectorHistoryWeightedScore_transport _ β t a hβ ht κ

end QuantitativePaper
