module
public import QuantitativePaper.VectorAdditiveL2
public import FourPapersCommon.IntegralGronwall

@[expose] public section

/-! Same-driver stability of the actual additive-noise state with distinct
bounded measurable drifts. Only an integrable time perturbation envelope is needed. -/
noncomputable section
open Set MeasureTheory FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 400000

theorem norm_vectorAdditiveState_sub_le_of_L1Drift
    (d e : VectorAdditiveDriftData n) (σ : ℝ) (x0 : Field n) (T : ℝ≥0)
    (a : ℝ→ℝ) (ha : IntervalIntegrable a volume 0 T)
    (ha0 : ∀s∈Icc (0 : ℝ) T,0≤a s)
    (hde : ∀r : ℝ≥0,r≤T→∀p x,‖d.drift r p x-e.drift r p x‖≤a r)
    (r : ℝ≥0) (hr : r≤T) (sample : VectorDisorderBrownianSample n) :
    ‖vectorAdditiveState d σ x0 T r sample-vectorAdditiveState e σ x0 T r sample‖≤
      (∫s in (0 : ℝ)..(T : ℝ),a s)*Real.exp ((e.spatialLip : ℝ)*r) := by
  let X:ℝ→Field n:=fun s=>vectorAdditiveState d σ x0 T s.toNNReal sample
  let Y:ℝ→Field n:=fun s=>vectorAdditiveState e σ x0 T s.toNNReal sample
  have hX : Continuous X := (continuous_vectorAdditiveState d σ x0 T sample).comp continuous_real_toNNReal
  have hY : Continuous Y := (continuous_vectorAdditiveState e σ x0 T sample).comp continuous_real_toNNReal
  let f:ℝ→ℝ:=fun s=>‖X s-Y s‖
  have hf : Continuous f := (hX.sub hY).norm
  let δ:ℝ:=∫s in (0 : ℝ)..(T : ℝ),a s
  have hδ : 0≤δ := intervalIntegral.integral_nonneg T.coe_nonneg ha0
  let F:ℝ→Field n:=fun s=>d.drift s.toNNReal sample.1 (X s)
  let G:ℝ→Field n:=fun s=>e.drift s.toNNReal sample.1 (Y s)
  have hFi : ∀u : ℝ,IntervalIntegrable F volume 0 u := by
    intro u
    apply (intervalIntegrable_const (c := (d.bound : ℝ))).mono_fun'
      (d.measurable.comp (continuous_real_toNNReal.measurable.prodMk
        (measurable_const.prodMk hX.measurable))).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun s=>d.norm_le _ _ _
  have hGi : ∀u : ℝ,IntervalIntegrable G volume 0 u := by
    intro u
    apply (intervalIntegrable_const (c := (e.bound : ℝ))).mono_fun'
      (e.measurable.comp (continuous_real_toNNReal.measurable.prodMk
        (measurable_const.prodMk hY.measurable))).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun s=>e.norm_le _ _ _
  have hineq : ∀u∈Icc (0 : ℝ) T,f u≤δ+(e.spatialLip : ℝ)*(∫s in 0..u,f s) := by
    intro u hu
    have hun : u.toNNReal≤T := by
      rw [←NNReal.coe_le_coe,Real.coe_toNNReal u hu.1]
      exact hu.2
    have hXu:=vectorAdditiveState_equation d σ x0 T u.toNNReal hun sample
    have hYu:=vectorAdditiveState_equation e σ x0 T u.toNNReal hun sample
    rw [Real.coe_toNNReal u hu.1] at hXu hYu
    have heq : X u-Y u=∫s in 0..u,F s-G s := by
      change vectorAdditiveState d σ x0 T u.toNNReal sample-
        vectorAdditiveState e σ x0 T u.toNNReal sample=_
      rw [hXu,hYu,add_sub_add_left_eq_sub]
      exact (intervalIntegral.integral_sub (hFi u) (hGi u)).symm
    have hp : ∀s∈Ioc (0 : ℝ) u,‖F s-G s‖≤a s+(e.spatialLip : ℝ)*f s := by
      intro s hs
      have hsn : s.toNNReal≤T := by
        rw [←NNReal.coe_le_coe,Real.coe_toNNReal s hs.1.le]
        exact hs.2.trans hu.2
      have hpert:=hde s.toNNReal hsn sample.1 (X s)
      rw [Real.coe_toNNReal s hs.1.le] at hpert
      have hlip:‖e.drift s.toNNReal sample.1 (X s)-e.drift s.toNNReal sample.1 (Y s)‖≤
          (e.spatialLip : ℝ)*‖X s-Y s‖ := by
        simpa only [dist_eq_norm] using (e.lipschitz s.toNNReal sample.1).dist_le_mul (X s) (Y s)
      have htri:=dist_triangle (d.drift s.toNNReal sample.1 (X s))
        (e.drift s.toNNReal sample.1 (X s)) (e.drift s.toNNReal sample.1 (Y s))
      simp only [dist_eq_norm] at htri
      exact htri.trans (add_le_add hpert hlip)
    change ‖X u-Y u‖≤_
    rw [heq]
    calc
      _≤∫s in 0..u,a s+(e.spatialLip : ℝ)*f s :=
        intervalIntegral.norm_integral_le_of_norm_le hu.1
          (Filter.Eventually.of_forall fun s hs=>hp s hs)
          ((ha.mono_set (by simpa only [uIcc_of_le T.coe_nonneg] using
            (uIcc_subset_Icc ⟨le_rfl,T.coe_nonneg⟩ hu))).add
              ((hf.intervalIntegrable 0 u).const_mul _))
      _=(∫s in 0..u,a s)+(e.spatialLip : ℝ)*(∫s in 0..u,f s) := by
        rw [intervalIntegral.integral_add (ha.mono_set (by
            simpa only [uIcc_of_le T.coe_nonneg] using (uIcc_subset_Icc ⟨le_rfl,T.coe_nonneg⟩ hu)))
          ((hf.intervalIntegrable 0 u).const_mul _),intervalIntegral.integral_const_mul]
      _≤δ+(e.spatialLip : ℝ)*(∫s in 0..u,f s) := by
        have hm := intervalIntegral.integral_mono_interval le_rfl hu.1 hu.2
          ((ae_restrict_mem measurableSet_Ioc).mono fun s hs=>ha0 s ⟨hs.1.le,hs.2⟩) ha
        exact add_le_add hm le_rfl
  have hb:=le_exp_of_integral_le f hf T δ e.spatialLip hδ e.spatialLip.coe_nonneg
    (fun s _=>norm_nonneg _) hineq (r : ℝ) ⟨r.coe_nonneg,show (r : ℝ)≤T from hr⟩
  simpa only [f,X,Y,δ,Real.toNNReal_coe] using hb

end QuantitativePaper
