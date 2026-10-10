module
public import QuantitativePaper.VectorControlDerivative
public import QuantitativePaper.VectorMeasureStateConvergence

@[expose] public section

/-! Uniform continuity of the genuine optimal feedback under CDF-L¹
convergence, including actual probability mixing with atoms. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem parisiCDFDistance_mix_left (μ ν : Paper.ParisiMeasure) (lam : ℝ)
    (hlam : lam ∈ Icc (0 : ℝ) 1) :
    Paper.parisiCDFDistance (Paper.parisiMix μ ν lam) μ = lam*Paper.parisiCDFDistance ν μ := by
  unfold Paper.parisiCDFDistance
  have he : (fun r : ℝ => ‖Paper.parisiCDF (Paper.parisiMix μ ν lam) r-Paper.parisiCDF μ r‖) =
      fun r => lam*‖Paper.parisiCDF ν r-Paper.parisiCDF μ r‖ := by
    funext r
    rw [Paper.parisiCDF_mix μ ν lam r hlam]
    rw [show (1-lam)*Paper.parisiCDF μ r+lam*Paper.parisiCDF ν r-Paper.parisiCDF μ r =
      lam*(Paper.parisiCDF ν r-Paper.parisiCDF μ r) from by ring]
    rw [norm_mul,Real.norm_of_nonneg hlam.1]
  simp only [Real.norm_eq_abs] at he
  rw [he,intervalIntegral.integral_const_mul]

theorem tendsto_parisiCDFDistance_mix_left (μ ν : Paper.ParisiMeasure) :
    Tendsto (fun lam => Paper.parisiCDFDistance (Paper.parisiMix μ ν lam) μ)
      (𝓝[Icc (0 : ℝ) 1] 0) (𝓝 0) := by
  have h0 : Tendsto (fun lam : ℝ => lam) (𝓝[Icc (0 : ℝ) 1] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hh := h0.mul_const (Paper.parisiCDFDistance ν μ)
  apply (show Tendsto (fun lam : ℝ => lam*Paper.parisiCDFDistance ν μ)
    (𝓝[Icc (0 : ℝ) 1] 0) (𝓝 0) from by simpa using hh).congr'
  filter_upwards [self_mem_nhdsWithin] with lam hlam
  exact (parisiCDFDistance_mix_left μ ν lam hlam).symm

def vectorFeedbackStabilityModulus (n : ℕ) (β t D : ℝ) : ℝ :=
  let c := (1-t)*β^2
  let K := 2*((n : ℝ)*c+n)
  K*Real.sqrt D+(n : ℝ)*c*Real.exp (c*n)*(Real.sqrt n*D+K*Real.sqrt D)

theorem norm_vectorMeasureFeedbackControl_sub_le (μ ν : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) (r : ℝ≥0) (hr : r ≤ 1)
    (sample : VectorDisorderBrownianSample n) :
    ‖vectorMeasureFeedbackControl μ β t ht r sample-vectorMeasureFeedbackControl ν β t ht r sample‖ ≤
      vectorFeedbackStabilityModulus n β t (Paper.parisiCDFDistance μ ν) := by
  let q : Paper.Overlap := projIcc (0 : ℝ) 1 zero_le_one r
  let K : ℝ := 2*((n : ℝ)*((1-t)*β^2)+(n : ℝ))
  let D : ℝ := K*Real.sqrt (Paper.parisiCDFDistance μ ν)
  have hD : 0 ≤ D := by dsimp only [D,K]; positivity
  have hgrad (q : Paper.Overlap) (p : Couplings n × ℝ) (x : Field n) :
      ‖vectorMeasureGradient μ β t q p x-vectorMeasureGradient ν β t q p x‖ ≤ D := by
    simpa only [D,K,← dist_eq_norm] using vectorMeasureGradient_CDFDistance_dist_le μ ν β t ht q p x
  have hs := norm_vectorMeasureState_sub_le μ ν β t ht D hD hgrad r hr sample
  have hl := (vectorMeasureGradient_lipschitz ν β t ht q sample.1).dist_le_mul
    (vectorMeasureState μ β t ht r sample) (vectorMeasureState ν β t ht r sample)
  rw [dist_eq_norm,dist_eq_norm,NNReal.coe_natCast] at hl
  unfold vectorMeasureFeedbackControl
  calc
    _ ≤ ‖vectorMeasureGradient μ β t q sample.1 (vectorMeasureState μ β t ht r sample)-
        vectorMeasureGradient ν β t q sample.1 (vectorMeasureState μ β t ht r sample)‖ +
      ‖vectorMeasureGradient ν β t q sample.1 (vectorMeasureState μ β t ht r sample)-
        vectorMeasureGradient ν β t q sample.1 (vectorMeasureState ν β t ht r sample)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ D+(n : ℝ)*((((1-t)*β^2)*Real.exp (((1-t)*β^2)*(n : ℝ)))*
        (Real.sqrt n*Paper.parisiCDFDistance μ ν+D)) := add_le_add (hgrad _ _ _)
      (hl.trans (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg n)))
    _ = _ := by unfold vectorFeedbackStabilityModulus; dsimp only [D,K]; ring

theorem tendstoUniformlyOn_vectorMeasureFeedbackControl_of_CDFDistance
    {ι : Type*} {L : Filter ι} {ν : ι → Paper.ParisiMeasure}
    (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t ≤ 1)
    (hD : Tendsto (fun i => Paper.parisiCDFDistance (ν i) μ) L (𝓝 0)) :
    TendstoUniformlyOn (fun i => fun z : ℝ≥0 × VectorDisorderBrownianSample n =>
      vectorMeasureFeedbackControl (ν i) β t ht z.1 z.2)
      (fun z => vectorMeasureFeedbackControl μ β t ht z.1 z.2) L (Icc (0 : ℝ≥0) 1 ×ˢ univ) := by
  have hc : Continuous (vectorFeedbackStabilityModulus n β t) := by
    unfold vectorFeedbackStabilityModulus; fun_prop
  have hzero : vectorFeedbackStabilityModulus n β t 0 = 0 := by
    simp [vectorFeedbackStabilityModulus]
  have hh := hc.continuousAt.tendsto.comp hD
  rw [hzero] at hh
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hh.eventually (gt_mem_nhds hε)] with i hi
  intro z hz
  rw [dist_comm,dist_eq_norm]
  exact (norm_vectorMeasureFeedbackControl_sub_le (ν i) μ β t ht z.1 hz.1.2 z.2).trans_lt hi

theorem tendstoUniformlyOn_vectorMeasureFeedbackControl_mix (μ ν : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) :
    TendstoUniformlyOn (fun lam => fun z : ℝ≥0 × VectorDisorderBrownianSample n =>
      vectorMeasureFeedbackControl (Paper.parisiMix μ ν lam) β t ht z.1 z.2)
      (fun z => vectorMeasureFeedbackControl μ β t ht z.1 z.2)
      (𝓝[Icc (0 : ℝ) 1] 0) (Icc (0 : ℝ≥0) 1 ×ˢ univ) :=
  tendstoUniformlyOn_vectorMeasureFeedbackControl_of_CDFDistance μ β t ht
    (tendsto_parisiCDFDistance_mix_left μ ν)

end QuantitativePaper
