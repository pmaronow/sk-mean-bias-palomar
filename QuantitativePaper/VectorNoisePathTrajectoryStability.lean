module
public import QuantitativePaper.VectorNoiseStatePathUniqueness
public import FourPapersCommon.IntegralGronwall

@[expose] public section

/-! Actual continuous-noise Picard stability needs drift comparison only
along the reference trajectory. Horizon restriction follows true uniqueness. -/
noncomputable section
open Set MeasureTheory FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem norm_vectorNoiseStatePath_sub_le_of_trajectory_forcing
    (d e : VectorAdditiveDriftData n) (σ : ℝ) (T : ℝ≥0)
    (p q : Couplings n×ℝ) (x y : Field n) (W : VectorWienerPath n)
    (a : ℝ→ℝ) (ha : IntervalIntegrable a volume 0 T)
    (ha0 : ∀s∈Icc (0:ℝ) T,0≤a s)
    (hde : ∀r : ℝ≥0,r≤T→
      ‖d.drift r p (vectorNoiseStatePath e σ T ((q,y),W) r)-
        e.drift r q (vectorNoiseStatePath e σ T ((q,y),W) r)‖≤a r)
    (r : ℝ) (hr : r∈Icc (0:ℝ) T) :
    ‖vectorNoiseStatePath d σ T ((p,x),W) r-vectorNoiseStatePath e σ T ((q,y),W) r‖≤
      (‖x-y‖+∫s in (0:ℝ)..(T:ℝ),a s)*Real.exp ((d.spatialLip:ℝ)*r) := by
  let X:=vectorNoiseStatePath d σ T ((p,x),W)
  let Y:=vectorNoiseStatePath e σ T ((q,y),W)
  have hX : Continuous X:=continuous_vectorNoiseStatePath d σ T _
  have hY : Continuous Y:=continuous_vectorNoiseStatePath e σ T _
  let f:ℝ→ℝ:=fun s=>‖X s-Y s‖
  have hf : Continuous f:=(hX.sub hY).norm
  let δ:ℝ:=‖x-y‖+∫s in (0:ℝ)..(T:ℝ),a s
  have hδ : 0≤δ:=add_nonneg (norm_nonneg _) (intervalIntegral.integral_nonneg T.coe_nonneg ha0)
  let F:ℝ→Field n:=fun s=>d.drift s.toNNReal p (X s)
  let G:ℝ→Field n:=fun s=>e.drift s.toNNReal q (Y s)
  have hFi (u : ℝ) : IntervalIntegrable F volume 0 u := by
    apply (intervalIntegrable_const (c:=(d.bound:ℝ))).mono_fun'
      (d.measurable.comp (continuous_real_toNNReal.measurable.prodMk
        (measurable_const.prodMk hX.measurable))).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun s=>d.norm_le _ _ _
  have hGi (u : ℝ) : IntervalIntegrable G volume 0 u := by
    apply (intervalIntegrable_const (c:=(e.bound:ℝ))).mono_fun'
      (e.measurable.comp (continuous_real_toNNReal.measurable.prodMk
        (measurable_const.prodMk hY.measurable))).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun s=>e.norm_le _ _ _
  have hineq (u : ℝ) (hu : u∈Icc (0:ℝ) T) : f u≤δ+(d.spatialLip:ℝ)*(∫s in 0..u,f s) := by
    have hXu:=vectorNoiseStatePath_equation d σ T ((p,x),W) u hu
    have hYu:=vectorNoiseStatePath_equation e σ T ((q,y),W) u hu
    have heq : X u-Y u=(x-y)+∫s in 0..u,F s-G s := by
      rw [show X u= x+σ • vectorContinuousNoise W u+∫s in 0..u,F s from hXu,
        show Y u= y+σ • vectorContinuousNoise W u+∫s in 0..u,G s from hYu,
        intervalIntegral.integral_sub (hFi u) (hGi u)]
      abel
    have hp (s : ℝ) (hs : s∈Ioc (0:ℝ) u) : ‖F s-G s‖≤a s+(d.spatialLip:ℝ)*f s := by
      have hsn : s.toNNReal≤T := by
        rw [←NNReal.coe_le_coe,Real.coe_toNNReal s hs.1.le]
        exact hs.2.trans hu.2
      have hd:=hde s.toNNReal hsn
      rw [Real.coe_toNNReal s hs.1.le] at hd
      have hl : ‖d.drift s.toNNReal p (X s)-d.drift s.toNNReal p (Y s)‖≤
          (d.spatialLip:ℝ)*f s := by
        simpa only [dist_eq_norm,f] using (d.lipschitz s.toNNReal p).dist_le_mul (X s) (Y s)
      exact (norm_sub_le_norm_sub_add_norm_sub _ (d.drift s.toNNReal p (Y s)) _).trans
        (by simpa only [add_comm] using add_le_add hl hd)
    have hsub : IntervalIntegrable a volume 0 u := ha.mono_set (by
      simpa only [uIcc_of_le T.coe_nonneg] using uIcc_subset_Icc ⟨le_rfl,T.coe_nonneg⟩ hu)
    change ‖X u-Y u‖≤_
    rw [heq]
    calc
      _≤‖x-y‖+‖∫s in 0..u,F s-G s‖:=norm_add_le _ _
      _≤‖x-y‖+∫s in 0..u,a s+(d.spatialLip:ℝ)*f s :=
        add_le_add le_rfl (intervalIntegral.norm_integral_le_of_norm_le hu.1
          (.of_forall fun s hs=>hp s hs) (hsub.add ((hf.intervalIntegrable 0 u).const_mul _)))
      _=‖x-y‖+(∫s in 0..u,a s)+(d.spatialLip:ℝ)*(∫s in 0..u,f s) := by
        rw [intervalIntegral.integral_add hsub ((hf.intervalIntegrable 0 u).const_mul _),
          intervalIntegral.integral_const_mul]
        ring
      _≤_ := by
        have hm:=intervalIntegral.integral_mono_interval le_rfl hu.1 hu.2
          ((ae_restrict_mem measurableSet_Ioc).mono fun s hs=>ha0 s ⟨hs.1.le,hs.2⟩) ha
        exact add_le_add (add_le_add le_rfl hm) le_rfl
  exact le_exp_of_integral_le f hf T δ d.spatialLip hδ d.spatialLip.coe_nonneg
    (fun s _=>norm_nonneg _) hineq r hr

theorem vectorNoiseStatePath_horizon_eq (d : VectorAdditiveDriftData n) (σ : ℝ)
    (T U : ℝ≥0) (hTU : T≤U) (z : VectorNoiseInitialData n) (r : ℝ)
    (hr : r∈Icc (0:ℝ) T) :
    vectorNoiseStatePath d σ T z r=vectorNoiseStatePath d σ U z r := by
  exact (vectorNoiseStatePath_unique d σ T z (vectorNoiseStatePath d σ U z)
    (continuous_vectorNoiseStatePath d σ U z)
    (fun s hs=>vectorNoiseStatePath_equation d σ U z s ⟨hs.1,hs.2.trans hTU⟩) r hr).symm

end QuantitativePaper
