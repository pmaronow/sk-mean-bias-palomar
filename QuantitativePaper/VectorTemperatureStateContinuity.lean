module
public import QuantitativePaper.VectorTemperatureGradientContinuity
public import QuantitativePaper.VectorTemperatureStateStability
public import QuantitativePaper.VectorMeasureState

@[expose] public section

/-! True continuity of the arbitrary-profile optimal diffusion in the
physical interpolation parameter on the same Gaussian/Wiener sample space. -/
noncomputable section
open Set Filter MeasureTheory FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem continuous_vectorMeasureDrift_temperature (μ : Paper.ParisiMeasure) (β : ℝ)
    (r : NNReal) (p : Couplings n × ℝ) (x : Field n) :
    Continuous (fun t : Iio (1 : ℝ) => vectorMeasureDrift μ β t t.property.le r p x) := by
  let q : Paper.Overlap := projIcc (0 : ℝ) 1 zero_le_one r
  have hi : Continuous (fun t : Iio (1 : ℝ) => (t,x)) := continuous_id.prodMk continuous_const
  have hg := (continuous_vectorMeasureGradient_temperature_field (n := n) μ β q p).comp hi
  have hc : Continuous (fun t : Iio (1 : ℝ) => (1-(t : ℝ))*β^2*Paper.parisiCDF μ r) := by fun_prop
  have h := hc.smul hg
  simpa only [Function.comp_def,Pi.smul_def',q,vectorMeasureDrift] using h

theorem continuous_vectorMeasureState_temperature (μ : Paper.ParisiMeasure) (β : ℝ)
    (r : NNReal) (hr : r ≤ 1) (sample : VectorDisorderBrownianSample n) :
    Continuous (fun t : Iio (1 : ℝ) => vectorMeasureState μ β t t.property.le r sample) := by
  rw [continuous_iff_continuousAt]
  intro t0
  let d := fun u : Iio (1 : ℝ) => vectorMeasureDriftData (n := n) μ β u u.property.le
  let σ := fun u : Iio (1 : ℝ) => Real.sqrt ((1-(u : ℝ))*β^2)
  let Y := fun s : ℝ => vectorMeasureState μ β t0 t0.property.le s.toNNReal sample
  have hY : Continuous Y := (continuous_vectorMeasureState μ β t0 t0.property.le sample).comp continuous_real_toNNReal
  let a := fun u : Iio (1 : ℝ) => fun s : ℝ =>
    ‖(d u).drift s.toNNReal sample.1 (Y s)-(d t0).drift s.toNNReal sample.1 (Y s)‖
  have hameas (u : Iio (1 : ℝ)) : Measurable (a u) :=
    ((d u).measurable.comp (continuous_real_toNNReal.measurable.prodMk
      (measurable_const.prodMk hY.measurable))).sub
      ((d t0).measurable.comp (continuous_real_toNNReal.measurable.prodMk
        (measurable_const.prodMk hY.measurable))) |>.norm
  have hab (u : Iio (1 : ℝ)) (s : ℝ) : a u s ≤ (d u).bound+(d t0).bound :=
    (norm_sub_le _ _).trans (add_le_add ((d u).norm_le _ _ _) ((d t0).norm_le _ _ _))
  have hai (u : Iio (1 : ℝ)) : IntervalIntegrable (a u) volume 0 1 :=
    (intervalIntegrable_const (c := ((d u).bound : ℝ)+((d t0).bound : ℝ))).mono_fun'
      (hameas u).aestronglyMeasurable (.of_forall fun s => by
        change ‖a u s‖ ≤ ((d u).bound : ℝ)+((d t0).bound : ℝ)
        rw [Real.norm_of_nonneg (show 0 ≤ a u s from norm_nonneg _)]
        exact hab u s)
  have hI : Tendsto (fun u => ∫ s in (0 : ℝ)..1, a u s) (𝓝 t0) (𝓝 0) := by
    have hcont : ContinuousAt (fun u => ∫ s in (0 : ℝ)..1, a u s) t0 := by
      simp_rw [intervalIntegral.integral_of_le zero_le_one]
      let C := (((2-(t0 : ℝ))*β^2)*Real.sqrt (n : ℝ))+((d t0).bound : ℝ)
      apply continuousAt_of_dominated (bound := fun _ => C)
      · exact .of_forall fun u => (hameas u).aestronglyMeasurable.restrict
      · have hloc : ∀ᶠ u : Iio (1 : ℝ) in 𝓝 t0, (t0 : ℝ)-1 < (u : ℝ) :=
          continuous_subtype_val.continuousAt.tendsto.eventually (lt_mem_nhds (by linarith))
        filter_upwards [hloc] with u hu
        exact .of_forall fun s => by
          rw [Real.norm_of_nonneg (norm_nonneg _)]
          apply (hab u s).trans
          change ((1-(u : ℝ))*β^2)*Real.sqrt (n : ℝ)+((d t0).bound : ℝ) ≤ C
          dsimp only [C]
          apply add_le_add
          · rw [mul_assoc,mul_assoc]
            apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          · exact le_rfl
      · exact integrable_const _
      · exact .of_forall fun s =>
          ((continuous_vectorMeasureDrift_temperature μ β s.toNNReal sample.1 (Y s)).sub continuous_const).norm.continuousAt
    have hz : (∫ s in (0 : ℝ)..1, a t0 s) = 0 := by simp [a]
    simpa only [hz] using hcont.tendsto
  obtain ⟨B,hnoise⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : NNReal) 1) (continuous_disorderVectorBrownian sample).continuousOn
  have hB : 0 ≤ B := (norm_nonneg _).trans (hnoise 0 (by constructor <;> norm_num))
  have hσ : Continuous σ := by dsimp [σ]; fun_prop
  have hδ : Tendsto (fun u => |σ u-σ t0| *B+∫ s in (0 : ℝ)..1, a u s) (𝓝 t0) (𝓝 0) := by
    simpa only [sub_self,abs_zero,zero_mul,zero_add] using
      ((hσ.continuousAt.tendsto.sub_const (σ t0)).abs.mul_const B).add hI
  have hexp : Continuous (fun u : Iio (1 : ℝ) => Real.exp (((d u).spatialLip : ℝ)*r)) := by
    change Continuous (fun u : Iio (1 : ℝ) => Real.exp (((1-(u : ℝ))*β^2*(n : ℝ))*r))
    fun_prop
  have hbound := hδ.mul hexp.continuousAt.tendsto
  simp only [zero_mul] at hbound
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hbound
  intro u
  exact norm_vectorAdditiveState_sub_le_of_pathDriftNoise (d u) (d t0) (σ u) (σ t0) 0 1 sample B hB
    (fun s hs => hnoise s ⟨zero_le,hs⟩) (a u) (hai u)
    (fun s _ => norm_nonneg _) (fun s _ => by
      simp only [a,Y,Real.toNNReal_coe]
      change ‖(d u).drift s sample.1 (vectorMeasureState μ β t0 t0.property.le s sample)-
        (d t0).drift s sample.1 (vectorMeasureState μ β t0 t0.property.le s sample)‖ ≤
        ‖(d u).drift s sample.1 (vectorMeasureState μ β t0 t0.property.le s sample)-
          (d t0).drift s sample.1 (vectorMeasureState μ β t0 t0.property.le s sample)‖
      rfl) r hr

end QuantitativePaper
