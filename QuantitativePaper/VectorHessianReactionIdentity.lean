module
public import QuantitativePaper.VectorHessianReactionGrid
public import QuantitativePaper.VectorMeanHessianTrace
public import QuantitativePaper.VectorGradientSquareIdentity

@[expose] public section

/-! Actual expected Hessian reaction for every probability profile.
The finite-cell Itô source is passed through the genuine dyadic spatial jets
and CDF convergence; no reaction or monotonicity hypothesis is supplied. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology BigOperators
namespace QuantitativePaper
open QuantitativeFollowup Paper
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem tendsto_vectorDyadicFixedHessianMean (μ : ParisiMeasure) (β t outer : ℝ)
    (ht : t ≤ 1) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun j=>vectorDyadicFixedHessianMean (n:=n) μ β t outer ht j r) atTop
      (𝓝 (vectorMeanHessianTrace (n:=n) μ β t outer ht ⟨r,hr⟩)) := by
  unfold vectorDyadicFixedHessianMean vectorMeanHessianTrace
  rw [projIcc_of_mem zero_le_one hr]
  apply Tendsto.div_const
  apply tendsto_finset_sum
  intro l _
  exact tendsto_expected_vectorFiniteTailHessian_diagonal μ β t outer ht ⟨r,hr⟩ l

theorem vectorMeanHessianReaction_intervalIntegrable (μ : ParisiMeasure)
    (β t outer : ℝ) (ht : t ≤ 1) (a b : ℝ) :
    IntervalIntegrable (fun x=>-parisiCDF μ x*vectorMeanOverlapDerivative (n:=n) μ β t outer ht
      (projIcc 0 1 zero_le_one x)) volume a b :=
  ((parisiCDF_monotone μ).intervalIntegrable).neg.mul_continuousOn
    (((continuous_vectorMeanOverlapDerivative μ β t outer ht).comp continuous_projIcc).continuousOn)

theorem vectorMeanHessianTrace_tail_integral (hn : 0 < n) (μ : ParisiMeasure)
    (β t outer : ℝ) (hβ : β ≠ 0) (ht : t < 1) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    vectorMeanHessianTrace (n:=n) μ β t outer ht.le ⟨1,zero_le_one,le_rfl⟩-
      vectorMeanHessianTrace (n:=n) μ β t outer ht.le ⟨r,hr⟩=
      ∫x in r..1,-parisiCDF μ x*vectorMeanOverlapDerivative (n:=n) μ β t outer ht.le
        (projIcc 0 1 zero_le_one x) := by
  have h1:=tendsto_vectorDyadicFixedHessianMean (n:=n) μ β t outer ht.le (r:=1) ⟨zero_le_one,le_rfl⟩
  have hrm:=tendsto_vectorDyadicFixedHessianMean (n:=n) μ β t outer ht.le hr
  have hI:=tendsto_integral_vectorDyadicFixedHessianSource (n:=n) μ β t outer ht.le hr ⟨zero_le_one,le_rfl⟩
  have he:=(h1.sub hrm).sub hI |>.norm
  have hD:=(tendsto_parisiCDFDistance_grid μ).comp tendsto_vectorDyadicIndex
  have hE:Tendsto (fun j=>((1-t)*β^2)*vectorSpatialJetBound n 3*(Real.sqrt n*parisiCDFDistance μ
        (parisiGridMeasure μ (vectorDyadicIndex j))+vectorDyadicFixedGradientError (n:=n) β t j)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero,zero_add] using
      ((hD.const_mul (Real.sqrt n)).add (tendsto_vectorDyadicFixedGradientError (n:=n) β t)).const_mul
        (((1-t)*β^2)*vectorSpatialJetBound n 3)
  have hb:=le_of_tendsto_of_tendsto he hE (.of_forall fun j=>vectorDyadicFixedHessian_tail_bound hn μ β t outer hβ ht j hr)
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hb (norm_nonneg _)))

/-- Literal normalized expected-trace reaction, including atoms and endpoints. -/
theorem vectorMeanHessianTrace_interval_integral (μ : ParisiMeasure)
    (β t outer : ℝ) (hβ : β ≠ 0) (ht : t < 1) (r q : Overlap) :
    vectorMeanHessianTrace (n:=n) μ β t outer ht.le q-
      vectorMeanHessianTrace (n:=n) μ β t outer ht.le r=
      ∫x in (r : ℝ)..(q : ℝ),-parisiCDF μ x*vectorMeanOverlapDerivative (n:=n) μ β t outer ht.le
        (projIcc 0 1 zero_le_one x) := by
  by_cases hn : n=0
  · subst n
    simp only [vectorMeanHessianTrace,Finset.univ_eq_empty,Finset.sum_empty,Nat.cast_zero,div_zero,
      sub_self,vectorMeanOverlapDerivative,mul_zero,zero_mul,intervalIntegral.integral_zero]
  · have hrI:=vectorMeanHessianTrace_tail_integral (Nat.pos_of_ne_zero hn) μ β t outer hβ ht r.property
    have hqI:=vectorMeanHessianTrace_tail_integral (Nat.pos_of_ne_zero hn) μ β t outer hβ ht q.property
    have htel:=intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
      (vectorMeanHessianReaction_intervalIntegrable (n:=n) μ β t outer ht.le r q)
      (vectorMeanHessianReaction_intervalIntegrable (n:=n) μ β t outer ht.le q 1)
    linarith

theorem vectorMeanHessianTrace_antitone (μ : ParisiMeasure) (β t outer : ℝ)
    (hβ : β ≠ 0) (ht : t < 1) :
    Antitone (vectorMeanHessianTrace (n:=n) μ β t outer ht.le) := by
  intro r q hrq
  have hi:=vectorMeanHessianTrace_interval_integral (n:=n) μ β t outer hβ ht r q
  have hn : 0 ≤ ∫x in (r : ℝ)..(q : ℝ),parisiCDF μ x*
      vectorMeanOverlapDerivative (n:=n) μ β t outer ht.le (projIcc 0 1 zero_le_one x):=
    intervalIntegral.integral_nonneg_of_forall hrq (fun x=>mul_nonneg
      (parisiCDF_nonneg μ x) (vectorMeanOverlapDerivative_nonneg μ β t outer ht.le _))
  simp_rw [neg_mul] at hi
  rw [intervalIntegral.integral_neg] at hi
  linarith

/-- The paper's physical Hessian trace b is genuinely nonincreasing. -/
theorem responseMeanHessian_antitone (μ : ParisiMeasure) (β t lam : ℝ)
    (hβ : 0 < β) (ht : t < 1) :
    Antitone (responseMeanHessian (n:=n) μ β t lam ht.le) := by
  intro r q hrq
  rw [responseMeanHessian_eq_meanTrace,responseMeanHessian_eq_meanTrace]
  exact mul_le_mul_of_nonneg_left
    (vectorMeanHessianTrace_antitone (n:=n) μ β t (lam/β) hβ.ne' ht hrq) hβ.le

/-- Literal energy-normalized trace reaction, with the true averaged curvature. -/
theorem responseMeanHessian_interval_integral (μ : ParisiMeasure)
    (β t lam : ℝ) (hβ : β ≠ 0) (ht : t < 1) (r q : Overlap) :
    responseMeanHessian (n:=n) μ β t lam ht.le r-
      responseMeanHessian (n:=n) μ β t lam ht.le q=
      β*(1-t)*∫x in (r : ℝ)..(q : ℝ),parisiCDF μ x*
        responseAveragedCurvature (n:=n) μ β t lam ht.le (projIcc 0 1 zero_le_one x) := by
  rw [responseMeanHessian_eq_meanTrace,responseMeanHessian_eq_meanTrace]
  have hi:=vectorMeanHessianTrace_interval_integral (n:=n) μ β t (lam/β) hβ ht r q
  calc
    _= -β*(vectorMeanHessianTrace (n:=n) μ β t (lam/β) ht.le q-
        vectorMeanHessianTrace (n:=n) μ β t (lam/β) ht.le r):=by ring
    _= -β*(∫x in (r : ℝ)..(q : ℝ),-parisiCDF μ x*vectorMeanOverlapDerivative (n:=n) μ β t (lam/β) ht.le
        (projIcc 0 1 zero_le_one x)):=by rw [hi]
    _= _:=by
      rw [←intervalIntegral.integral_const_mul,←intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x _
      unfold vectorMeanOverlapDerivative responseAveragedCurvature
      ring

end QuantitativePaper
