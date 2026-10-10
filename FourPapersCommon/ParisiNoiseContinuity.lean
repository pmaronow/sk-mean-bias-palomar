module
public import FourPapersCommon.IntegralDriftStability
public import Paper.ParisiSelectedState
public import Paper.ParisiStateStability
public import FRSB.GlobalMeasureStability
public import Paper.ParisiCDFIntegral

@[expose] public section

/-! Joint dependence of the actual integral Picard state on a weak overlap
measure and a continuous driving path. No state-continuity premise is used. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal
namespace FourPapersCommon
open Paper Paper.IntegralPicard
set_option maxHeartbeats 1000000

def parisiNoiseStatePath (β h : ℝ) (μ : ParisiMeasure) :
    C(Icc (0 : ℝ) 1, ℝ) → C(Icc (0 : ℝ) 1, ℝ) :=
  Paper.parisiStatePath β h μ (fun t x => Paper.parisiGradient β μ (t,x))
    (Paper.continuous_parisiGradient β μ)
    (fun t x => Paper.norm_parisiGradient_le_one β μ (t,x))
    (Paper.lipschitzWith_parisiGradient_all β μ) 1 zero_le_one

theorem continuous_parisiNoiseStatePath (β h : ℝ) (μ : ParisiMeasure) :
    Continuous (parisiNoiseStatePath β h μ) :=
  Paper.continuous_parisiStatePath β h μ _ _ _ _ 1 zero_le_one

theorem measurable_parisiNoiseStatePath (β h : ℝ) (μ : ParisiMeasure) :
    Measurable (parisiNoiseStatePath β h μ) :=
  (continuous_parisiNoiseStatePath β h μ).measurable

@[simp] theorem parisiNoiseStatePath_canonical (β h : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (ω : Paper.BrownianSample) (t : Icc (0 : ℝ) 1) :
    parisiNoiseStatePath β h μ (Paper.canonicalBrownianPath ω) t =
      Paper.selectedParisiStateReal β h hβ μ ω t := by
  exact Paper.parisiStatePath_apply β h μ _ _ _ _ 1 zero_le_one _ t

private theorem noise_drift_measure_bound (β : ℝ) (μ ν : ParisiMeasure)
    (W : ℝ → ℝ) (t x : ℝ) :
    dist (Paper.parisiNoiseDrift β μ (fun s y => Paper.parisiGradient β μ (s,y)) W t x)
      (Paper.parisiNoiseDrift β ν (fun s y => Paper.parisiGradient β ν (s,y)) W t x) ≤
      β^2*(‖Paper.parisiGradientBCF β μ - Paper.parisiGradientBCF β ν‖ +
        ‖Paper.parisiCDF μ t - Paper.parisiCDF ν t‖) := by
  let y := x+β*W t
  have he : Paper.parisiNoiseDrift β μ (fun s y => Paper.parisiGradient β μ (s,y)) W t x -
      Paper.parisiNoiseDrift β ν (fun s y => Paper.parisiGradient β ν (s,y)) W t x =
      β^2*(Paper.parisiCDF μ t*(Paper.parisiGradient β μ (t,y)-Paper.parisiGradient β ν (t,y)) +
        (Paper.parisiCDF μ t-Paper.parisiCDF ν t)*Paper.parisiGradient β ν (t,y)) := by
    dsimp [Paper.parisiNoiseDrift, y]
    ring
  rw [dist_eq_norm, he, norm_mul, Real.norm_of_nonneg (sq_nonneg β)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg β)
  apply (norm_add_le _ _).trans
  simp only [norm_mul]
  have hc : ‖Paper.parisiCDF μ t‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (Paper.parisiCDF_nonneg μ t)]
    exact Paper.parisiCDF_le_one μ t
  have hg := Paper.norm_parisiSlabExtend_sub_le (by norm_num)
    (Paper.parisiGradientBCF β μ) (Paper.parisiGradientBCF β ν) (t,y)
  change ‖Paper.parisiGradient β μ (t,y)-Paper.parisiGradient β ν (t,y)‖ ≤ _ at hg
  have hb := Paper.norm_parisiGradient_le_one β ν (t,y)
  simpa only [one_mul, mul_one] using add_le_add
    (mul_le_mul hc hg (norm_nonneg _) (by norm_num))
    (mul_le_mul_of_nonneg_left hb (norm_nonneg _))

/-- A finite measure-stability constant depending only on beta. -/
def parisiNoiseMeasureConstant (β : ℝ) : ℝ :=
  integratedSensitivity (Paper.parisiDriftConstant β) 1 (Paper.parisiStateStabilityIndex β) /
    (1-(β^2)^(Paper.parisiStateStabilityIndex β)/(Paper.parisiStateStabilityIndex β).factorial)*β^2

theorem parisiNoiseMeasureConstant_nonneg (β : ℝ) : 0 ≤ parisiNoiseMeasureConstant β := by
  unfold parisiNoiseMeasureConstant
  exact mul_nonneg (div_nonneg (integratedSensitivity_nonneg zero_le_one _)
    (sub_pos.mpr (Paper.parisiStateStabilityIndex_spec β)).le) (sq_nonneg β)

theorem parisiNoiseStatePath_measure_dist_le (β h : ℝ) (μ ν : ParisiMeasure)
    (W : C(Icc (0 : ℝ) 1,ℝ)) :
    dist (parisiNoiseStatePath β h μ W) (parisiNoiseStatePath β h ν W) ≤
      parisiNoiseMeasureConstant β *
        (‖Paper.parisiGradientBCF β μ-Paper.parisiGradientBCF β ν‖ +
          Paper.parisiCDFDistance μ ν) := by
  let noise := Paper.parisiNoiseExtension zero_le_one W
  have hnoise := Paper.continuous_parisiNoiseExtension zero_le_one W
  let vf := fun s x => Paper.parisiGradient β μ (s,x)
  let vg := fun s x => Paper.parisiGradient β ν (s,x)
  let hf := Paper.isBoundedMeasurableDrift_parisiNoiseDrift β μ vf
    (Paper.continuous_parisiGradient β μ) (fun t x => Paper.norm_parisiGradient_le_one β μ (t,x))
      (Paper.lipschitzWith_parisiGradient_all β μ) noise hnoise
  let hg := Paper.isBoundedMeasurableDrift_parisiNoiseDrift β ν vg
    (Paper.continuous_parisiGradient β ν) (fun t x => Paper.norm_parisiGradient_le_one β ν (t,x))
      (Paper.lipschitzWith_parisiGradient_all β ν) noise hnoise
  let d := ‖Paper.parisiGradientBCF β μ-Paper.parisiGradientBCF β ν‖
  let e := fun t => β^2*(d+‖Paper.parisiCDF μ t-Paper.parisiCDF ν t‖)
  have hei : IntervalIntegrable e volume 0 1 :=
    (intervalIntegrable_const.add ((Paper.parisiCDF_intervalIntegrable μ 0 1).sub
      (Paper.parisiCDF_intervalIntegrable ν 0 1)).norm).const_mul _
  have hbound := solution_dist_le_of_integrated_drift_bound (h := h) zero_le_one hf hg e hei
    (fun _ _ => mul_nonneg (sq_nonneg β) (add_nonneg (norm_nonneg _) (norm_nonneg _)))
    (fun t _ x => noise_drift_measure_bound β μ ν noise t x)
    (Paper.parisiStateStabilityIndex β) (by
      simpa only [Paper.coe_parisiDriftConstant, mul_one] using Paper.parisiStateStabilityIndex_spec β)
  have heq : (∫ t in 0..1, e t) = β^2*(d+Paper.parisiCDFDistance μ ν) := by
    dsimp only [e]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
      intervalIntegrable_const ((Paper.parisiCDF_intervalIntegrable μ 0 1).sub
        (Paper.parisiCDF_intervalIntegrable ν 0 1)).norm, intervalIntegral.integral_const]
    simp only [sub_zero, one_smul]
    rfl
  rw [heq] at hbound
  apply (ContinuousMap.dist_le (mul_nonneg (parisiNoiseMeasureConstant_nonneg β)
    (add_nonneg (norm_nonneg _) (Paper.parisiCDFDistance_nonneg μ ν)))).mpr
  intro t
  change dist ((solution (h := h) zero_le_one hf) t+β*W t)
    ((solution (h := h) zero_le_one hg) t+β*W t) ≤ _
  rw [dist_add_right]
  have heval := ContinuousMap.dist_apply_le_dist (f := ODE.FunSpace.toContinuousMap
    (solution (h := h) zero_le_one hf)) (g := ODE.FunSpace.toContinuousMap
      (solution (h := h) zero_le_one hg)) t
  apply (heval.trans hbound).trans_eq
  dsimp only [parisiNoiseMeasureConstant, d]
  simp only [Paper.coe_parisiDriftConstant, mul_one]
  ring

theorem tendsto_parisiNoiseStatePath_of_weak_and_noise {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (β h : ℝ) (μn : ι → ParisiMeasure) (μ : ParisiMeasure)
    (hμ : Tendsto μn L (𝓝 μ)) (Wn : ι → C(Icc (0 : ℝ) 1,ℝ)) (W : C(Icc (0 : ℝ) 1,ℝ))
    (hW : Tendsto Wn L (𝓝 W)) :
    Tendsto (fun i => parisiNoiseStatePath β h (μn i) (Wn i)) L (𝓝 (parisiNoiseStatePath β h μ W)) := by
  have hg := ((FRSB.continuous_gradientBCF β).continuousAt.tendsto.comp hμ).sub_const
    (Paper.parisiGradientBCF β μ)
  have hgn : Tendsto (fun i => ‖Paper.parisiGradientBCF β (μn i)-Paper.parisiGradientBCF β μ‖)
      L (𝓝 0) := by simpa using hg.norm
  have hCDF := FRSB.tendsto_parisiCDFDistance_of_tendsto hμ
  have he : Tendsto (fun i => dist (parisiNoiseStatePath β h (μn i) (Wn i))
      (parisiNoiseStatePath β h μ (Wn i))) L (𝓝 0) := by
    apply squeeze_zero (fun _ => dist_nonneg) (fun i => parisiNoiseStatePath_measure_dist_le β h (μn i) μ (Wn i))
    simpa using tendsto_const_nhds.mul (hgn.add hCDF)
  exact tendsto_of_tendsto_of_dist
    ((continuous_parisiNoiseStatePath β h μ).continuousAt.tendsto.comp hW) (by
      simpa only [Function.comp_def, dist_comm] using he)

end FourPapersCommon
