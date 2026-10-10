module
public import QuantitativePaper.VectorHessianReactionIdentity

@[expose] public section

/-! The sharp actual mean-response bound. Antitonicity and the true
self-overlap energy identity give the precise constant, for all profiles. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon
open scoped NNReal Topology BigOperators
namespace QuantitativePaper
open QuantitativeFollowup Paper
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem responseMeanHessian_nonneg (μ : ParisiMeasure) (β t lam : ℝ)
    (hβ : 0 ≤ β) (ht : t ≤ 1) (q : Overlap) :
    0 ≤ responseMeanHessian (n:=n) μ β t lam ht q := by
  unfold responseMeanHessian responseHessianTrace
  apply mul_nonneg (div_nonneg zero_le_one (Nat.cast_nonneg _))
  exact integral_nonneg fun sample=>mul_nonneg hβ
    (vectorMeasureHessianMatrix_posSemidef μ β t ht q sample).trace_nonneg

theorem continuous_responseMeanHessian (μ : ParisiMeasure) (β t lam : ℝ)
    (ht : t ≤ 1) : Continuous (responseMeanHessian (n:=n) μ β t lam ht) := by
  have he : responseMeanHessian (n:=n) μ β t lam ht=
      fun q=>β*vectorMeanHessianTrace (n:=n) μ β t (lam/β) ht q := by
    funext q
    exact responseMeanHessian_eq_meanTrace μ β t lam ht q
  rw [he]
  exact (continuous_vectorMeanHessianTrace μ β t (lam/β) ht).const_mul β

theorem vectorMeanOverlapDerivative_eq_responseCurvature (μ : ParisiMeasure)
    (β t lam : ℝ) (ht : t ≤ 1) (q : Overlap) :
    vectorMeanOverlapDerivative (n:=n) μ β t (lam/β) ht q=
      (1-t)*responseAveragedCurvature (n:=n) μ β t lam ht q := by
  unfold vectorMeanOverlapDerivative responseAveragedCurvature
  ring

/-- Exact dimension-independent upper bound, with physical q in (0,1]. -/
theorem responseMeanHessian_upper (hn : 0 < n) (μ : ParisiMeasure)
    (β t lam : ℝ) (hβ : 0 < β) (ht : t < 1) (q : Overlap) (hq : 0 < (q : ℝ)) :
    responseMeanHessian (n:=n) μ β t lam ht.le q ≤ 1/Real.sqrt ((1-t)*(q : ℝ)) := by
  let b:=responseMeanHessian (n:=n) μ β t lam ht.le
  let D:=fun x : ℝ=>vectorMeanOverlapDerivative (n:=n) μ β t (lam/β) ht.le (projIcc 0 1 zero_le_one x)
  have hb:=responseMeanHessian_antitone (n:=n) μ β t lam hβ ht
  have hbnonneg (x : Overlap) : 0 ≤ b x:=responseMeanHessian_nonneg μ β t lam hβ.le ht.le x
  have hmono: (∫x in (0:ℝ)..(q : ℝ),(1-t)*(b q)^2) ≤ ∫x in (0:ℝ)..(q : ℝ),D x := by
    apply intervalIntegral.integral_mono_on hq.le intervalIntegrable_const
      (((continuous_vectorMeanOverlapDerivative μ β t (lam/β) ht.le).comp continuous_projIcc).intervalIntegrable 0 q)
    intro x hx
    have hx01 : x ∈ Icc (0 : ℝ) 1:=⟨hx.1,hx.2.trans q.property.2⟩
    let p:Overlap:=⟨x,hx01⟩
    have hbp:b q ≤ b p:=hb hx.2
    have hs:(b q)^2 ≤ (b p)^2:=pow_le_pow_left₀ (hbnonneg q) hbp 2
    have hc:=responseAveragedCurvature_ge_mean_square hn μ β t lam ht.le p
    have hscale:=mul_le_mul_of_nonneg_left (hs.trans hc) (sub_pos.mpr ht).le
    simpa only [Function.comp_def,D,projIcc_of_mem zero_le_one hx01,
      vectorMeanOverlapDerivative_eq_responseCurvature] using hscale
  have he:=vectorMeanOverlapReal_interval_integral (n:=n) μ β t (lam/β) hβ.ne' ht
    (r:=0) (q:=q) ⟨le_rfl,zero_le_one⟩ q.property
  have hS0:0 ≤ vectorMeanOverlapReal (n:=n) μ β t (lam/β) ht.le 0:=by
    exact (vectorMeanOverlap_nonneg_le_one μ β t (lam/β) ht.le _).1
  have hS1:vectorMeanOverlapReal (n:=n) μ β t (lam/β) ht.le (q : ℝ) ≤ 1:=by
    exact (vectorMeanOverlap_nonneg_le_one μ β t (lam/β) ht.le _).2
  have henergy:∫x in (0:ℝ)..(q : ℝ),D x ≤ 1:=by
    change (∫x in (0:ℝ)..(q : ℝ),vectorMeanOverlapDerivative (n:=n) μ β t (lam/β) ht.le
      (projIcc 0 1 zero_le_one x)) ≤ 1
    linarith
  have hsq : ((1-t)*(q : ℝ))*(b q)^2 ≤ 1:=by
    have hh:=hmono.trans henergy
    simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hh
    nlinarith
  have hrq : 0 < (1-t)*(q : ℝ):=mul_pos (sub_pos.mpr ht) hq
  have hroot:0 < Real.sqrt ((1-t)*(q : ℝ)):=Real.sqrt_pos.mpr hrq
  apply (le_div_iff₀ hroot).mpr
  have heq:=Real.sq_sqrt hrq.le
  have hsprod : (b q*Real.sqrt ((1-t)*(q : ℝ)))^2 ≤ 1:=by
    rw [mul_pow,heq]
    nlinarith
  change b q*Real.sqrt ((1-t)*(q : ℝ)) ≤ 1
  nlinarith

end QuantitativePaper
