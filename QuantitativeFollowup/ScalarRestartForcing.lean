module
public import QuantitativeFollowup.ScalarRestartMeasure
public import QuantitativeFollowup.ScalarFieldJointContinuity
public import QuantitativeFollowup.ScalarRestartFlow

@[expose] public section

/-! The actual measurable-time restart drift converges in time-L¹ along
any fixed continuous path when its measure and restart level converge. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped NNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

theorem scalarRestartDriftField_sub_bound (β : ℝ) (μ ν : Paper.ParisiMeasure)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (r x : ℝ) :
    ‖scalarRestartDriftField β μ a ha r x-scalarRestartDriftField β ν b hb r x‖ ≤
      β^2*(‖parisiCDF (parisiRestartMeasure μ a ha) r-parisiCDF (parisiRestartMeasure ν b hb) r‖+
        ‖parisiGradient β μ (a+r,x)-parisiGradient β ν (b+r,x)‖) := by
  have he : scalarRestartDriftField β μ a ha r x-scalarRestartDriftField β ν b hb r x=
      β^2*((parisiCDF (parisiRestartMeasure μ a ha) r-parisiCDF (parisiRestartMeasure ν b hb) r)*
        parisiGradient β μ (a+r,x)+parisiCDF (parisiRestartMeasure ν b hb) r*
          (parisiGradient β μ (a+r,x)-parisiGradient β ν (b+r,x))) := by
    dsimp only [scalarRestartDriftField]
    ring
  rw [he,norm_mul,Real.norm_of_nonneg (sq_nonneg β)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg β)
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_mul,Real.norm_of_nonneg (parisiCDF_nonneg _ _)]
  exact add_le_add (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (norm_parisiGradient_le_one β μ (a+r,x)) (norm_nonneg _))
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (parisiCDF_le_one _ _) (norm_nonneg _))

theorem scalarRestartDriftField_reference_integrable (β : ℝ) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : 0 ≤ a) (X : ℝ → ℝ) (hX : Continuous X) (u v : ℝ) :
    IntervalIntegrable (fun r => scalarRestartDriftField β μ a ha r (X r)) volume u v :=
  intervalIntegrable_const.mono_fun'
    ((scalarRestartDriftField_data β μ a ha).measurable.comp
      (measurable_id.prodMk hX.measurable)).aestronglyMeasurable
    (.of_forall fun r => (scalarRestartDriftField_data β μ a ha).norm_le r _)

theorem tendsto_scalarRestartDriftField_reference_gap {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (β : ℝ) (μn : ι → Paper.ParisiMeasure) (μ : Paper.ParisiMeasure)
    (hμ : Tendsto μn L (𝓝 μ)) (an : ι → ℝ) (a : ℝ)
    (han : ∀ i,0 ≤ an i) (ha : 0 ≤ a) (hA : Tendsto an L (𝓝 a))
    (X : ℝ → ℝ) (hX : Continuous X) :
    Tendsto (fun i => ∫ r in 0..1,
      ‖scalarRestartDriftField β (μn i) (an i) (han i) r (X r)-
        scalarRestartDriftField β μ a ha r (X r)‖) L (𝓝 0) := by
  let τ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  let G := fun i r => ‖parisiGradient β (μn i) (an i+r,X r)-parisiGradient β μ (a+r,X r)‖
  have hGi (i : ι) : IntervalIntegrable (G i) volume 0 1 :=
    (((continuous_parisiGradient β (μn i)).comp
      ((continuous_const.add continuous_id).prodMk hX)).sub
        ((continuous_parisiGradient β μ).comp
          ((continuous_const.add continuous_id).prodMk hX))).norm.intervalIntegrable 0 1
  have hGlim : Tendsto (fun i => ∫ r in 0..1,G i r) L (𝓝 0) := by
    have hh := tendsto_integral_filter_of_dominated_convergence (μ := τ) (fun _ => (2 : ℝ))
      (.of_forall fun i => (hGi i).1.aestronglyMeasurable)
      (.of_forall fun i => .of_forall fun r => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact (norm_sub_le _ _).trans (by
          linarith [norm_parisiGradient_le_one β (μn i) (an i+r,X r),
            norm_parisiGradient_le_one β μ (a+r,X r)])) (integrable_const _)
      (.of_forall fun r => by
        have harg := hμ.prodMk_nhds ((hA.add_const r).prodMk_nhds (tendsto_const_nhds (x := X r)))
        have hg := (continuous_parisiGradient_measure_joint β).continuousAt.tendsto.comp harg
        simpa only [G,Function.comp_def,sub_self,norm_zero] using (hg.sub_const (parisiGradient β μ (a+r,X r))).norm)
    simpa only [τ,intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1),integral_zero] using hh
  have hCDF := tendsto_parisiRestartMeasure_CDFDistance μn μ hμ an a han ha hA
  have hb (i : ι) : (∫ r in 0..1,‖scalarRestartDriftField β (μn i) (an i) (han i) r (X r)-
        scalarRestartDriftField β μ a ha r (X r)‖) ≤
      β^2*(Paper.parisiCDFDistance (parisiRestartMeasure (μn i) (an i) (han i))
        (parisiRestartMeasure μ a ha)+∫ r in 0..1,G i r) := by
    have hh := intervalIntegral.integral_mono_on (zero_le_one : (0 : ℝ) ≤ 1)
      ((scalarRestartDriftField_reference_integrable β (μn i) (an i) (han i) X hX 0 1).sub
        (scalarRestartDriftField_reference_integrable β μ a ha X hX 0 1)).norm
      (((parisiCDF_abs_diff_intervalIntegrable _ _ 0 1).add (hGi i)).const_mul (β^2))
      (fun r _ => by simpa only [G,Real.norm_eq_abs] using
        scalarRestartDriftField_sub_bound β (μn i) μ (an i) a (han i) ha r (X r))
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add
      (parisiCDF_abs_diff_intervalIntegrable _ _ 0 1) (hGi i)] at hh
    exact hh
  apply squeeze_zero (fun i => intervalIntegral.integral_nonneg (zero_le_one : (0 : ℝ) ≤ 1)
    (fun _ _ => norm_nonneg _)) hb
  simpa only [add_zero,mul_zero] using (tendsto_const_nhds (x := β^2)).mul (hCDF.add hGlim)

end QuantitativeFollowup
