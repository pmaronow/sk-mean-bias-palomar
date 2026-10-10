module
public import QuantitativePaper.ResponseDyadicCrossingStage
public import QuantitativePaper.VectorFiniteResponseLower
public import QuantitativePaper.VectorDyadicMovingTrace
public import QuantitativePaper.VectorHessianReactionIdentity

@[expose] public section

/-! The literal averaged-curvature lower bound for every actual admissible
measure profile. A true CDF quantile selects the finite mass crossing;
genuine tilted-diffusion trace convergence passes its conditional Gaussian
bound to the actual profile. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Paper
open scoped BigOperators Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 1800000
variable {n : ℕ}

theorem responseMeanHessian_lower (hn : 0 < n) (μ : ParisiMeasure)
    (β t lam U : ℝ) (hβ : 1 ≤ β) (ht : t ∈ Ico 0 1)
    (hlam : 0 ≤ lam) (hfloor : lam ≤ β*parisiCDF μ 0)
    (q : Overlap) (hU : β*parisiCDF μ q ≤ U) :
    responseCurvatureConstant U ≤ responseMeanHessian (n:=n) μ β t lam ht.2.le q := by
  have hβp : 0 < β := lt_of_lt_of_le (by norm_num) hβ
  have ha : lam/β ≤ parisiCDF μ 0 := (div_le_iff₀ hβp).mpr (by simpa only [mul_comm] using hfloor)
  obtain ⟨T,hqT,hout,hin,hroot⟩ := exists_responseCrossingTime μ β (lam/β) U hβ ha q hU
  have hfinite (j : ℕ) : responseCurvatureConstant U ≤
      (1/(n : ℝ))*∫sample : VectorDisorderBrownianSample n,vectorDyadicMovingTrace μ β t ht.2.le T j sample
        ∂vectorFiniteDisorderTilt (parisiGridRSBScheme μ (vectorDyadicIndex j)) β t (lam/β) := by
    let s := parisiGridRSBScheme μ (vectorDyadicIndex j)
    let N := vectorDyadicTimeIndex T j
    have hN : N ≤ (vectorDyadicIndex j+1)+2 := (vectorDyadicTimeIndex_le T j).trans (by omega)
    have hNp : 0 < N := by dsimp [N,vectorDyadicTimeIndex];omega
    obtain ⟨hrootfloor,hout',hin'⟩ := responseDyadicCrossingStage μ β (lam/β) U hβp ha T hout hin hroot j
    have hh := vectorFiniteNodeTrace_expected_lower hn s β t (lam/β) U hβp ht
      (div_nonneg hlam hβp.le) hrootfloor (by simp [s,parisiGridRSBScheme]) N hNp hN hout' hin'
    convert hh using 2
    congr 1
    funext sample
    unfold vectorDyadicMovingTrace
    simp_rw [vectorDyadicMovingHessian_eq_node]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change β*(vectorFieldHessian s β t sample.1 ((vectorDyadicIndex j+1)+2-N)
      (vectorDyadicState μ β t ht.2.le j (vectorDyadicTime T j) sample)
      (EuclideanSpace.single i 1)) i =
      vectorFiniteNodeCurvature s β t N i
        (vectorFiniteJointState s β t ht.2.le (s.q N).toNNReal sample)
    unfold vectorFiniteNodeCurvature vectorFiniteJointState vectorDyadicState
    rw [show s.q N=(parisiGridRound (vectorDyadicIndex j) T : ℝ) from
      vectorDyadicTimeIndex_node μ T j]
    rfl
  have hT := ge_of_tendsto (tendsto_integral_vectorDyadicMovingTrace (n:=n) μ β t lam ht.2.le T)
    (.of_forall hfinite)
  exact hT.trans (responseMeanHessian_antitone μ β t lam hβp ht.2 hqT)

theorem responseAveragedCurvature_lower (hn : 0 < n) (μ : ParisiMeasure)
    (β t lam U : ℝ) (hβ : 1 ≤ β) (ht : t ∈ Ico 0 1)
    (hlam : 0 ≤ lam) (hfloor : lam ≤ β*parisiCDF μ 0)
    (q : Overlap) (hU : β*parisiCDF μ q ≤ U) :
    (responseCurvatureConstant U)^2 ≤ responseAveragedCurvature (n:=n) μ β t lam ht.2.le q := by
  have hh := responseMeanHessian_lower hn μ β t lam U hβ ht hlam hfloor q hU
  exact (pow_le_pow_left₀ (responseCurvatureConstant_pos U).le hh 2).trans
    (responseAveragedCurvature_ge_mean_square hn μ β t lam ht.2.le q)

end QuantitativePaper
