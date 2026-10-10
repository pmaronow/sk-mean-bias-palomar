module
public import QuantitativePaper.VectorGradientSquareGrid
public import QuantitativeFollowup.VectorOverlapDeficit

@[expose] public section

/-! The literal all-profile mean-overlap integral evolution is obtained
from true finite-cell Itô, actual fractional tilt, endpoint closure,
moving-node telescoping, and genuine uniform jet/CDF approximation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology BigOperators
namespace QuantitativePaper
open SpinGlass.Targets QuantitativeFollowup Paper
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem tendsto_vectorDyadicFixedSquareMoment (μ : ParisiMeasure) (β t outer : ℝ)
    (ht : t≤1) {r : ℝ} (hr : r∈Icc (0:ℝ) 1) :
    Tendsto (fun j=>vectorDyadicFixedSquareMoment (n:=n) μ β t outer ht j r) atTop
      (𝓝 (vectorMeanOverlapReal (n:=n) μ β t outer ht r)) := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t outer ht
  let q:Overlap:=⟨r,hr⟩
  unfold vectorDyadicFixedSquareMoment vectorMeanOverlapReal vectorMeanOverlap
  rw [projIcc_of_mem zero_le_one hr]
  apply Tendsto.div_const
  apply tendsto_finset_sum
  intro l _
  have hX:Measurable (vectorMeasureState (n:=n) μ β t ht r.toNNReal):=
    ((stronglyAdapted_vectorMeasureState μ β t ht r.toNNReal).measurable).mono
      ((vectorBrownianFiltration n).le _) le_rfl
  have hmap:Measurable (fun sample : VectorDisorderBrownianSample n=>(q,(sample.1,
      vectorMeasureState μ β t ht r.toNNReal sample))):=measurable_const.prodMk (measurable_fst.prodMk hX)
  apply tendsto_integral_of_dominated_convergence (fun _ : VectorDisorderBrownianSample n=>(1:ℝ))
  · intro j
    have hm:=((EuclideanSpace.proj l).continuous.measurable.comp
      (measurable_vectorFiniteTailGradient (parisiGridRSBScheme μ (vectorDyadicIndex j)) β t)).comp hmap
    exact (hm.pow_const 2).aestronglyMeasurable
  · exact integrable_const _
  · intro j
    exact .of_forall fun sample=>by
      rw [norm_pow,Real.norm_eq_abs]
      apply pow_le_one₀ (abs_nonneg _)
      rw [vectorDyadicTailGradient,vectorFiniteTailGradient_eq_magnetization]
      exact vectorMagnetization_component_bound _ β t _ _ _ l
  · exact .of_forall fun sample=>by
      have hh:=(EuclideanSpace.proj l).continuous.tendsto
        (vectorMeasureGradient μ β t q sample.1 (vectorMeasureState μ β t ht r.toNNReal sample)) |>.comp
          (tendsto_vectorDyadicTailGradient μ β t ht q sample.1 (vectorMeasureState μ β t ht r.toNNReal sample))
      exact hh.pow 2

theorem tendsto_vectorDyadicFixedGradientError (β t : ℝ) :
    Tendsto (vectorDyadicFixedGradientError (n:=n) β t) atTop (𝓝 0) := by
  unfold vectorDyadicFixedGradientError
  simpa only [mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one vectorGradientDecay_pos.le vectorGradientDecay_lt_one).const_mul
      ((4*(n:ℝ)*((1-t)*β^2)+2*n)/(1-vectorGradientDecay))

theorem vectorMeanOverlapReal_tail_integral (hn : 0<n) (μ : ParisiMeasure)
    (β t outer : ℝ) (hβ : β≠0) (ht : t<1) {r : ℝ} (hr : r∈Icc (0:ℝ) 1) :
    vectorMeanOverlapReal (n:=n) μ β t outer ht.le 1-vectorMeanOverlapReal (n:=n) μ β t outer ht.le r=
      ∫x in r..1,vectorMeanOverlapDerivative (n:=n) μ β t outer ht.le (projIcc 0 1 zero_le_one x) := by
  have h1:=tendsto_vectorDyadicFixedSquareMoment (n:=n) μ β t outer ht.le (r:=1) ⟨zero_le_one,le_rfl⟩
  have hrm:=tendsto_vectorDyadicFixedSquareMoment (n:=n) μ β t outer ht.le hr
  have hI:=tendsto_integral_vectorDyadicFixedEnergySource (n:=n) μ β t outer ht.le r 1
  have he:=(h1.sub hrm).sub hI |>.norm
  have hD:=(tendsto_parisiCDFDistance_grid μ).comp tendsto_vectorDyadicIndex
  have hE:Tendsto (fun j=>2*((1-t)*β^2)*(n:ℝ)*(Real.sqrt n*parisiCDFDistance μ
        (parisiGridMeasure μ (vectorDyadicIndex j))+vectorDyadicFixedGradientError (n:=n) β t j)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero,zero_add] using
      ((hD.const_mul (Real.sqrt n)).add (tendsto_vectorDyadicFixedGradientError (n:=n) β t)).const_mul
        (2*((1-t)*β^2)*(n:ℝ))
  have hb:=le_of_tendsto_of_tendsto he hE (.of_forall fun j=>vectorDyadicFixedSquare_tail_bound hn μ β t outer hβ ht j hr)
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hb (norm_nonneg _)))

theorem vectorMeanOverlapReal_interval_integral (μ : ParisiMeasure)
    (β t outer : ℝ) (hβ : β≠0) (ht : t<1) {r q : ℝ}
    (hr : r∈Icc (0:ℝ) 1) (hq : q∈Icc (0:ℝ) 1) :
    vectorMeanOverlapReal (n:=n) μ β t outer ht.le q-vectorMeanOverlapReal (n:=n) μ β t outer ht.le r=
      ∫x in r..q,vectorMeanOverlapDerivative (n:=n) μ β t outer ht.le (projIcc 0 1 zero_le_one x) := by
  by_cases hn : n=0
  · subst n
    simp only [vectorMeanOverlapReal,vectorMeanOverlap,Finset.univ_eq_empty,Finset.sum_empty,
      Nat.cast_zero,div_zero,sub_self,vectorMeanOverlapDerivative,mul_zero,zero_mul,
      intervalIntegral.integral_zero]
  · have hnpos:0<n:=Nat.pos_of_ne_zero hn
    have hrI:=vectorMeanOverlapReal_tail_integral hnpos μ β t outer hβ ht hr
    have hqI:=vectorMeanOverlapReal_tail_integral hnpos μ β t outer hβ ht hq
    have hc:Continuous (fun x : ℝ=>vectorMeanOverlapDerivative (n:=n) μ β t outer ht.le (projIcc 0 1 zero_le_one x)):=
      (continuous_vectorMeanOverlapDerivative μ β t outer ht.le).comp continuous_projIcc
    have htel:=intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
      (hc.intervalIntegrable r q) (hc.intervalIntegrable q 1)
    linarith

end QuantitativePaper
