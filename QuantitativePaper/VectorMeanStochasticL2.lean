module
public import QuantitativePaper.VectorMeanStochasticCross

@[expose] public section

/-! Literal stochastic identity dM=√c H dB for the actual arbitrary-profile
diffusion under the genuine fractional disorder tilt. The integral is
characterized by its actual adapted uniform Brownian left sums, which converge
in mean square and in probability on every physical interval. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon
open scoped NNReal ENNReal Topology BigOperators
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem vectorMeanLeftSum_error_square_expansion (hn : 0<n) (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (r q : Paper.Overlap) (hrq : r≤q) (N : ℕ) :
    (∫sample : VectorDisorderBrownianSample n,
      ‖vectorMeasureSpinMean μ β t ht.le q sample-vectorMeasureSpinMean μ β t ht.le r sample-
        vectorMeanLeftSum (n:=n) μ β t ht.le r q hrq N sample‖^2∂vectorMeasureDisorderTilt μ β t a)=
      ((n:ℝ)*∫s in (r:ℝ)..(q:ℝ),vectorMeanOverlapDerivative (n:=n) μ β t a ht.le (projIcc 0 1 zero_le_one s))-
      2*(∫sample : VectorDisorderBrownianSample n,inner ℝ (vectorMeasureSpinMean μ β t ht.le q sample-vectorMeasureSpinMean μ β t ht.le r sample)
        (vectorMeanLeftSum (n:=n) μ β t ht.le r q hrq N sample)∂vectorMeasureDisorderTilt μ β t a)+
      (∫sample : VectorDisorderBrownianSample n,‖vectorMeanLeftSum (n:=n) μ β t ht.le r q hrq N sample‖^2∂vectorMeasureDisorderTilt μ β t a) := by
  have := vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht.le
  have h := integral_norm_sub_sq_of_memLp_two
    ((memLp_vectorMeasureSpinMean μ β t a ht.le q).sub (memLp_vectorMeasureSpinMean μ β t a ht.le r))
    (memLp_vectorMeanLeftSum (n:=n) μ β t a ht.le r q hrq N)
  have h' := vectorMean_increment_variance_integral hn μ β t a hβ ht r q hrq
  rw [show vectorMeasureSpinMean (n:=n) μ β t ht.le q-vectorMeasureSpinMean μ β t ht.le r=
    (fun sample=>vectorMeasureSpinMean μ β t ht.le q sample-vectorMeasureSpinMean μ β t ht.le r sample) from rfl] at h
  rw [h'] at h
  exact h

theorem tendsto_vectorMeanLeftSum_L2 (hn : 0<n) (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (r q : Paper.Overlap) (hrq : r≤q) :
    Tendsto (fun N =>∫sample : VectorDisorderBrownianSample n,
      ‖vectorMeasureSpinMean μ β t ht.le q sample-vectorMeasureSpinMean μ β t ht.le r sample-
        vectorMeanLeftSum (n:=n) μ β t ht.le r q hrq N sample‖^2∂vectorMeasureDisorderTilt μ β t a)
      atTop (𝓝 0) := by
  simp_rw [vectorMeanLeftSum_error_square_expansion hn μ β t a hβ ht r q hrq]
  have hc := tendsto_vectorMeanLeftSum_cross_moment hn μ β t a hβ ht r q hrq
  have hs := tendsto_vectorMeanLeftSum_secondMoment hn μ β t a ht.le r q hrq
  have h := ((tendsto_const_nhds (x := (n:ℝ)*∫s in (r:ℝ)..(q:ℝ),
    vectorMeanOverlapDerivative (n:=n) μ β t a ht.le (projIcc 0 1 zero_le_one s))).sub (hc.const_mul 2)).add hs
  have hz : ((n:ℝ)*∫s in (r:ℝ)..(q:ℝ),vectorMeanOverlapDerivative (n:=n) μ β t a ht.le (projIcc 0 1 zero_le_one s))-
      2*((n:ℝ)*∫s in (r:ℝ)..(q:ℝ),vectorMeanOverlapDerivative (n:=n) μ β t a ht.le (projIcc 0 1 zero_le_one s))+
      ((n:ℝ)*∫s in (r:ℝ)..(q:ℝ),vectorMeanOverlapDerivative (n:=n) μ β t a ht.le (projIcc 0 1 zero_le_one s))=0 := by ring
  simpa only [hz] using h

theorem vectorMeasureSpinMean_stochastic_identity (hn : 0<n) (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (r q : Paper.Overlap) (hrq : r≤q) :
    TendstoInMeasure (vectorMeasureDisorderTilt (n:=n) μ β t a)
      (vectorMeanLeftSum (n:=n) μ β t ht.le r q hrq) atTop
      (fun sample =>vectorMeasureSpinMean μ β t ht.le q sample-vectorMeasureSpinMean μ β t ht.le r sample) := by
  have := vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht.le
  let P := vectorMeasureDisorderTilt (n:=n) μ β t a
  let U : VectorDisorderBrownianSample n→Field n := fun sample =>
    vectorMeasureSpinMean μ β t ht.le q sample-vectorMeasureSpinMean μ β t ht.le r sample
  have hU : MemLp U 2 P := (memLp_vectorMeasureSpinMean μ β t a ht.le q).sub (memLp_vectorMeasureSpinMean μ β t a ht.le r)
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  have hi (N : ℕ) : Integrable (fun sample =>‖vectorMeanLeftSum (n:=n) μ β t ht.le r q hrq N sample-U sample‖^2) P := by
    have h := ((memLp_vectorMeanLeftSum (n:=n) μ β t a ht.le r q hrq N).sub hU).integrable_norm_pow'
    convert h using 1
  have he (N : ℕ) : (∫sample : VectorDisorderBrownianSample n,‖vectorMeanLeftSum (n:=n) μ β t ht.le r q hrq N sample-U sample‖^2∂P)=
      ∫sample : VectorDisorderBrownianSample n,‖U sample-vectorMeanLeftSum (n:=n) μ β t ht.le r q hrq N sample‖^2∂P := by
    apply integral_congr_ae
    exact .of_forall fun sample => by
      change ‖vectorMeanLeftSum (n:=n) μ β t ht.le r q hrq N sample-U sample‖^2=
        ‖U sample-vectorMeanLeftSum (n:=n) μ β t ht.le r q hrq N sample‖^2
      rw [norm_sub_rev]
  have hb (N : ℕ) : P.real {sample | ε≤‖vectorMeanLeftSum (n:=n) μ β t ht.le r q hrq N sample-U sample‖}≤
      (∫sample : VectorDisorderBrownianSample n,‖U sample-vectorMeanLeftSum (n:=n) μ β t ht.le r q hrq N sample‖^2∂P)/ε^2 := by
    have h := mul_meas_ge_le_integral_of_nonneg (μ:=P)
      (.of_forall fun sample =>sq_nonneg ‖vectorMeanLeftSum (n:=n) μ β t ht.le r q hrq N sample-U sample‖) (hi N) (ε^2)
    have hset : {sample | ε≤‖vectorMeanLeftSum (n:=n) μ β t ht.le r q hrq N sample-U sample‖}⊆
        {sample | ε^2≤‖vectorMeanLeftSum (n:=n) μ β t ht.le r q hrq N sample-U sample‖^2} := by
      intro sample hs
      exact pow_le_pow_left₀ hε.le hs 2
    have hp := mul_le_mul_of_nonneg_left (measureReal_mono (μ:=P) hset) (sq_nonneg ε)
    apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
    rw [mul_comm]
    exact (hp.trans h).trans_eq (he N)
  apply squeeze_zero (fun _ =>measureReal_nonneg) hb
  simpa only [zero_div] using (tendsto_vectorMeanLeftSum_L2 hn μ β t a hβ ht r q hrq).div_const (ε^2)

end QuantitativePaper
