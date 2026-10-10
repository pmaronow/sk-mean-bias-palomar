module
public import FourPapersCommon.ParisiNoiseContinuity
public import FourPapersCommon.ParisiBetaUniformContinuity
public import FourPapersCommon.IntegralStateTemperature

@[expose] public section

/-! Joint temperature, weak-measure and driving-path continuity of the
actual selected integral diffusion. The quantitative comparison is pathwise
and permits CDF jumps. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal BoundedContinuousFunction
namespace FourPapersCommon
open Paper
set_option maxHeartbeats 1000000

theorem parisiNoiseStatePath_temperature_dist_le (β γ h : ℝ) (μ : ParisiMeasure)
    (W : C(Icc (0 : ℝ) 1,ℝ)) :
    dist (parisiNoiseStatePath β h μ W) (parisiNoiseStatePath γ h μ W)≤
      (|β-γ| *‖W‖+|β^2-γ^2|+γ^2*‖parisiGradientBCF β μ-parisiGradientBCF γ μ‖)*Real.exp (γ^2) := by
  let noise:=parisiNoiseExtension zero_le_one W
  have hnoise:=continuous_parisiNoiseExtension zero_le_one W
  let X (b : ℝ) : ℝ→ℝ:=parisiStateReal b h μ (fun t x=>parisiGradient b μ (t,x))
    (continuous_parisiGradient b μ) (fun t x=>norm_parisiGradient_le_one b μ (t,x))
    (lipschitzWith_parisiGradient_all b μ) 1 zero_le_one noise hnoise
  have hX (b : ℝ) : Continuous (X b) := continuous_parisiStateReal b h μ _ _ _ _ _ _ _ _
  have hXe (b : ℝ) (r : ℝ) (hr : r∈Icc (0 : ℝ) 1) :
      X b r=h+b*noise r+∫s in 0..r,b^2*parisiCDF μ s*parisiGradient b μ (s,X b s) :=
    parisiStateReal_integral_equation b h μ _ _ _ _ 1 zero_le_one noise hnoise hr
  have hg (r x : ℝ) : ‖parisiGradient β μ (r,x)-parisiGradient γ μ (r,x)‖≤
      ‖parisiGradientBCF β μ-parisiGradientBCF γ μ‖ :=
    norm_parisiSlabExtend_sub_le (by norm_num) _ _ _
  have he:=integral_state_temperature_bound β γ h (parisiCDF μ) (parisiCDF_monotone μ).measurable
    (parisiCDF_nonneg μ) (parisiCDF_le_one μ)
    (fun t x=>parisiGradient β μ (t,x)) (fun t x=>parisiGradient γ μ (t,x))
    (continuous_parisiGradient β μ) (continuous_parisiGradient γ μ)
    (fun t x=>norm_parisiGradient_le_one β μ (t,x)) (fun t x=>norm_parisiGradient_le_one γ μ (t,x))
    (lipschitzWith_parisiGradient_all γ μ) _ (norm_nonneg _) hg noise (X β) (X γ) (hX β) (hX γ)
    ‖W‖ (norm_nonneg _) (fun r _=>W.norm_coe_le_norm _) (hXe β) (hXe γ)
  apply (ContinuousMap.dist_le (by positivity)).mpr
  intro t
  rw [dist_eq_norm]
  have hp (b : ℝ) : parisiNoiseStatePath b h μ W t=X b t :=
    parisiStatePath_apply b h μ _ _ _ _ 1 zero_le_one W t
  rw [hp β,hp γ]
  exact he t t.property

theorem tendsto_parisiNoiseStatePath_of_temperature_weak_and_noise {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (β : ι→ℝ) (γ h : ℝ) (hγ : γ≠0) (hβ : Tendsto β L (𝓝 γ))
    (μn : ι→ParisiMeasure) (μ : ParisiMeasure) (hμ : Tendsto μn L (𝓝 μ))
    (Wn : ι→C(Icc (0 : ℝ) 1,ℝ)) (W : C(Icc (0 : ℝ) 1,ℝ)) (hW : Tendsto Wn L (𝓝 W)) :
    Tendsto (fun i=>parisiNoiseStatePath (β i) h (μn i) (Wn i)) L (𝓝 (parisiNoiseStatePath γ h μ W)) := by
  have hg:=tendsto_parisiGradientBCF_of_temperature_and_weak β γ hγ hβ μn μ hμ
  have hgfix:=(FRSB.continuous_gradientBCF γ).continuousAt.tendsto.comp hμ
  have hd : Tendsto (fun i=>‖parisiGradientBCF (β i) (μn i)-parisiGradientBCF γ (μn i)‖)
      L (𝓝 0) := by simpa only [Function.comp_def,sub_self,norm_zero] using (hg.sub hgfix).norm
  have herror : Tendsto (fun i=>dist (parisiNoiseStatePath (β i) h (μn i) (Wn i))
      (parisiNoiseStatePath γ h (μn i) (Wn i))) L (𝓝 0) := by
    apply squeeze_zero (fun _=>dist_nonneg)
      (fun i=>parisiNoiseStatePath_temperature_dist_le (β i) γ h (μn i) (Wn i))
    have hb0 : Tendsto (fun i=>|β i-γ|) L (𝓝 (0 : ℝ)) := by simpa using (hβ.sub_const γ).abs
    have hs0 : Tendsto (fun i=>|β i^2-γ^2|) L (𝓝 (0 : ℝ)) := by
      convert ((hβ.pow 2).sub_const (γ^2)).abs using 1; simp
    simpa only [zero_mul,mul_zero,zero_add] using
      (((hb0.mul hW.norm).add hs0).add (hd.const_mul (γ^2))).mul_const (Real.exp (γ^2))
  exact tendsto_of_tendsto_of_dist
    (tendsto_parisiNoiseStatePath_of_weak_and_noise γ h μn μ hμ Wn W hW)
    (by simpa only [Function.comp_def,dist_comm] using herror)

end FourPapersCommon
