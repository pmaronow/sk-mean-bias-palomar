module
public import QuantitativePaper.VectorGridProfileUniformThirdVariation
public import QuantitativePaper.VectorProfileEndpointInverse
public import QuantitativePaper.VectorMeasureTail

@[expose] public section

/-! Honest closed-segment finite profile jet bounds and actual uniform
profile approximation. Ordinary finite jets are bounded also at the
endpoints; the arbitrary-measure limit will use within derivatives there. -/
noncomputable section
open Set Filter
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorGridProfileTailFunction (μ ν : Paper.ParisiMeasure) (β t : ℝ)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) (j : ℕ) (θ : ℝ) : ℝ:=
  vectorProfileTailRecursion (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
    (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t q θ p (vectorDyadicIndex j+3) x

theorem contDiff_vectorGridProfileTailFunction (μ ν : Paper.ParisiMeasure) (β t : ℝ)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) (j : ℕ) :
    ContDiff ℝ ∞ (vectorGridProfileTailFunction μ ν β t q p x j) :=
  (contDiff_vectorProfileJointPotential_all_theta
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
    (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t q (vectorDyadicIndex j+3) le_rfl).comp
      (show ContDiff ℝ ∞ (fun θ : ℝ=>((θ,p),x)) by fun_prop)

theorem continuous_bound_on_closed_unit_interval (f : ℝ→ℝ) (hf : Continuous f)
    (C : ℝ) (hbound : ∀θ∈Ioo (0:ℝ) 1,‖f θ‖≤C) :
    ∀θ∈Icc (0:ℝ) 1,‖f θ‖≤C := by
  have hh : closure (Ioo (0:ℝ) 1)⊆{θ | ‖f θ‖≤C}:=
    closure_minimal hbound (isClosed_le hf.norm continuous_const)
  intro θ hθ
  apply hh
  simpa only [closure_Ioo zero_ne_one] using hθ

theorem norm_vectorGridProfileTailFunction_second_deriv_closed_le
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) :
    ∀θ∈Icc (0:ℝ) 1,‖deriv (deriv (vectorGridProfileTailFunction μ ν β t q p x j)) θ‖≤
      vectorProfileSecondReactionBound n β t := by
  have hf:=contDiff_vectorGridProfileTailFunction μ ν β t q p x j
  have h1 : ContDiff ℝ ∞ (deriv (vectorGridProfileTailFunction μ ν β t q p x j)):=hf.deriv'
  have h2 : ContDiff ℝ ∞ (deriv (deriv (vectorGridProfileTailFunction μ ν β t q p x j))):=h1.deriv'
  exact continuous_bound_on_closed_unit_interval _ h2.continuous _
    (fun θ hθ=>norm_vectorGridProfileTailRecursion_second_profile_deriv_le μ ν j β t hβ ht q p x θ hθ)

theorem norm_vectorGridProfileTailFunction_third_deriv_closed_le
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) :
    ∀θ∈Icc (0:ℝ) 1,‖deriv (deriv (deriv (vectorGridProfileTailFunction μ ν β t q p x j))) θ‖≤
      vectorProfileThirdReactionBound n β t := by
  have hf:=contDiff_vectorGridProfileTailFunction μ ν β t q p x j
  have h1 : ContDiff ℝ ∞ (deriv (vectorGridProfileTailFunction μ ν β t q p x j)):=hf.deriv'
  have h2 : ContDiff ℝ ∞ (deriv (deriv (vectorGridProfileTailFunction μ ν β t q p x j))):=h1.deriv'
  have h3 : ContDiff ℝ ∞ (deriv (deriv (deriv (vectorGridProfileTailFunction μ ν β t q p x j)))):=h2.deriv'
  exact continuous_bound_on_closed_unit_interval _ h3.continuous _
    (fun θ hθ=>norm_vectorGridProfileTailRecursion_third_profile_deriv_le μ ν j β t hβ ht q p x θ hθ)

theorem tendstoUniformlyOn_vectorGridProfileTailFunction
    (μ ν : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) :
    TendstoUniformlyOn (vectorGridProfileTailFunction μ ν β t q p x)
      (fun θ=>vectorMeasureTailPotential (Paper.parisiMix μ ν θ) β t q p x) atTop
        (Icc (0:ℝ) 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hh : Tendsto (fun j : ℕ=>(4*(n:ℝ)*((1-t)*β^2))*(1/2:ℝ)^j) atTop (𝓝 0):=by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
        (by norm_num : (1/2:ℝ)<1)).const_mul (4*(n:ℝ)*((1-t)*β^2))
  filter_upwards [hh.eventually (gt_mem_nhds hε)] with j hj
  intro θ hθ
  have he : vectorGridProfileTailFunction μ ν β t q p x j θ=
      vectorDyadicTailPotential (Paper.parisiMix μ ν θ) β t q j p x := by
    unfold vectorGridProfileTailFunction
    rw [vectorProfileTailRecursion_eq_scheme _ _ β t q θ hθ,
      vector_grid_profile_scheme_eq_mix μ ν (vectorDyadicIndex j) θ hθ]
    rfl
  rw [Real.dist_eq,abs_sub_comm,he]
  exact (vectorDyadicTailPotential_limit_abs_sub_le (Paper.parisiMix μ ν θ) β t q ht q.property j p x).trans_lt hj

end QuantitativePaper
