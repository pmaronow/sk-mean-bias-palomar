module
public import QuantitativePaper.VectorAdditiveStability

@[expose] public section

/-! Same-Wiener-driver stability for different initial fields. The drift
perturbation is tested on the actual reference path. -/
noncomputable section
open Set MeasureTheory FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1200000
variable {n : ℕ}

theorem norm_vectorAdditiveState_sub_le_of_initial_pathDrift
    (d e : VectorAdditiveDriftData n) (σ : ℝ) (x0 y0 : Field n) (T : NNReal)
    (sample : VectorDisorderBrownianSample n)
    (a : ℝ → ℝ) (ha : IntervalIntegrable a volume 0 T)
    (ha0 : ∀ s ∈ Icc (0 : ℝ) T, 0 ≤ a s)
    (hde : ∀ r : NNReal, r ≤ T →
      ‖d.drift r sample.1 (vectorAdditiveState e σ y0 T r sample)-
        e.drift r sample.1 (vectorAdditiveState e σ y0 T r sample)‖ ≤ a r)
    (r : NNReal) (hr : r ≤ T) :
    ‖vectorAdditiveState d σ x0 T r sample-vectorAdditiveState e σ y0 T r sample‖ ≤
      (‖x0-y0‖+∫ s in (0 : ℝ)..(T : ℝ), a s)*Real.exp ((d.spatialLip : ℝ)*r) := by
  let X := fun s : ℝ => vectorAdditiveState d σ x0 T s.toNNReal sample
  let Y := fun s : ℝ => vectorAdditiveState e σ y0 T s.toNNReal sample
  have hX : Continuous X := (continuous_vectorAdditiveState d σ x0 T sample).comp continuous_real_toNNReal
  have hY : Continuous Y := (continuous_vectorAdditiveState e σ y0 T sample).comp continuous_real_toNNReal
  let f := fun s : ℝ => ‖X s-Y s‖
  have hf : Continuous f := (hX.sub hY).norm
  let δ := ‖x0-y0‖+∫ s in (0 : ℝ)..(T : ℝ), a s
  have hδ : 0 ≤ δ := add_nonneg (norm_nonneg _)
    (intervalIntegral.integral_nonneg T.coe_nonneg ha0)
  let F := fun s : ℝ => d.drift s.toNNReal sample.1 (X s)
  let G := fun s : ℝ => e.drift s.toNNReal sample.1 (Y s)
  have hFi (u : ℝ) : IntervalIntegrable F volume 0 u :=
    (intervalIntegrable_const (c := (d.bound : ℝ))).mono_fun'
      (d.measurable.comp (continuous_real_toNNReal.measurable.prodMk
        (measurable_const.prodMk hX.measurable))).aestronglyMeasurable
      (.of_forall fun s => d.norm_le _ _ _)
  have hGi (u : ℝ) : IntervalIntegrable G volume 0 u :=
    (intervalIntegrable_const (c := (e.bound : ℝ))).mono_fun'
      (e.measurable.comp (continuous_real_toNNReal.measurable.prodMk
        (measurable_const.prodMk hY.measurable))).aestronglyMeasurable
      (.of_forall fun s => e.norm_le _ _ _)
  have hineq : ∀ u ∈ Icc (0 : ℝ) T, f u ≤ δ+(d.spatialLip : ℝ)*(∫ s in 0..u, f s) := by
    intro u hu
    have hun : u.toNNReal ≤ T := by
      rw [←NNReal.coe_le_coe,Real.coe_toNNReal u hu.1]; exact hu.2
    have hXu := vectorAdditiveState_equation d σ x0 T u.toNNReal hun sample
    have hYu := vectorAdditiveState_equation e σ y0 T u.toNNReal hun sample
    rw [Real.coe_toNNReal u hu.1] at hXu hYu
    have heq : X u-Y u = x0-y0+
        ∫ s in 0..u, F s-G s := by
      change vectorAdditiveState d σ x0 T u.toNNReal sample-
        vectorAdditiveState e σ y0 T u.toNNReal sample = _
      rw [hXu,hYu,intervalIntegral.integral_sub (hFi u) (hGi u)]
      dsimp only [F,G,X,Y]
      abel
    have hp : ∀ s ∈ Ioc (0 : ℝ) u, ‖F s-G s‖ ≤ a s+(d.spatialLip : ℝ)*f s := by
      intro s hs
      have hsn : s.toNNReal ≤ T := by
        rw [←NNReal.coe_le_coe,Real.coe_toNNReal s hs.1.le]; exact hs.2.trans hu.2
      have hpert := hde s.toNNReal hsn
      rw [Real.coe_toNNReal s hs.1.le] at hpert
      have hlip := (d.lipschitz s.toNNReal sample.1).norm_sub_le (X s) (Y s)
      have htri := norm_sub_le_norm_sub_add_norm_sub (d.drift s.toNNReal sample.1 (X s))
        (d.drift s.toNNReal sample.1 (Y s)) (e.drift s.toNNReal sample.1 (Y s))
      change ‖F s-G s‖ ≤ _ at htri
      dsimp only [f]
      exact htri.trans (by linarith)
    have hai : IntervalIntegrable a volume 0 u := ha.mono_set (by
      simpa only [uIcc_of_le T.coe_nonneg] using (uIcc_subset_Icc ⟨le_rfl,T.coe_nonneg⟩ hu))
    have hni : ‖∫ s in 0..u, F s-G s‖ ≤ ∫ s in 0..u, a s+(d.spatialLip : ℝ)*f s :=
      intervalIntegral.norm_integral_le_of_norm_le hu.1
        (.of_forall fun s hs => hp s hs) (hai.add ((hf.intervalIntegrable 0 u).const_mul _))

    have hm := intervalIntegral.integral_mono_interval le_rfl hu.1 hu.2
      ((ae_restrict_mem measurableSet_Ioc).mono fun s hs => ha0 s ⟨hs.1.le,hs.2⟩) ha
    change ‖X u-Y u‖ ≤ _
    rw [heq]
    calc
      _ ≤ ‖x0-y0‖+‖∫ s in 0..u, F s-G s‖ := norm_add_le _ _
      _ ≤ ‖x0-y0‖+∫ s in 0..u, a s+(d.spatialLip : ℝ)*f s := add_le_add le_rfl hni
      _ ≤ δ+(d.spatialLip : ℝ)*(∫ s in 0..u, f s) := by
        rw [intervalIntegral.integral_add hai ((hf.intervalIntegrable 0 u).const_mul _),
          intervalIntegral.integral_const_mul]
        dsimp only [δ]
        linarith
  have hb := le_exp_of_integral_le f hf T δ d.spatialLip hδ d.spatialLip.coe_nonneg
    (fun s _ => norm_nonneg _) hineq (r : ℝ) ⟨r.coe_nonneg,show (r : ℝ) ≤ T from hr⟩
  simpa only [f,X,Y,δ,Real.toNNReal_coe] using hb

end QuantitativePaper
