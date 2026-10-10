module
public import QuantitativePaper.VectorDirectionCovarianceEvolution
public import QuantitativePaper.ScalarFloorContinuity

@[expose] public section

/-! Directional covariance decay for bounded earlier-past directions. The
denominator is the literal squared-CDF integral, and its positivity follows
from an actual positive root mass. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon
open scoped NNReal ENNReal Topology
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem vectorDirectionCovariance_le_norm_moment (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap)
    (b : VectorDisorderBrownianSample n→Field n)
    (hb : MemLp b 2 (vectorMeasureDisorderTilt μ β t a)) :
    vectorDirectionCovariance μ β t a ht b q≤
      2*(n:ℝ)^2*(∫sample,‖b sample‖^2∂vectorMeasureDisorderTilt μ β t a) := by
  have hi := hb.norm.integrable_mul hb.norm
  change Integrable (fun sample=>‖b sample‖*‖b sample‖) _ at hi
  have hi' : Integrable (fun sample=>‖b sample‖^2) (vectorMeasureDisorderTilt μ β t a) := by
    simpa only [pow_two] using hi
  rw [←integral_const_mul]
  apply integral_mono_ae (integrable_vectorMeasureRandomCovariance μ β t a ht q b hb) (hi'.const_mul _)
  filter_upwards [vectorMeasureCovarianceQuadratic_uniform_bound μ β t a ht q] with sample hs
  exact (le_abs_self _).trans (hs (b sample))

theorem vectorDirectionDenominator_lower (μ : Paper.ParisiMeasure) (β t s : ℝ)
    (ht : t≤1) (hs : 0 ≤ s) (hμ : μ∈scalarFloor s)
    (r q : Paper.Overlap) (hrq : r≤q) :
    ((1-t)*β^2)*s^2*((q:ℝ)-r)≤
      ((1-t)*β^2)*∫u in (r:ℝ)..(q:ℝ),(Paper.parisiCDF μ u)^2 := by
  have hp : Monotone (fun u=>(Paper.parisiCDF μ u)^2) := fun x y hxy=>
    pow_le_pow_left₀ (Paper.parisiCDF_nonneg μ x) ((Paper.parisiCDF_monotone μ) hxy) 2
  have hI : ((q:ℝ)-r)*s^2≤∫u in (r:ℝ)..(q:ℝ),(Paper.parisiCDF μ u)^2 := by
    have hh := intervalIntegral.integral_mono_on (μ:=volume) hrq
      (f:=fun _ : ℝ=>s^2) intervalIntegrable_const hp.intervalIntegrable
      (fun u hu=>pow_le_pow_left₀ hs (scalarFloor_cdf_lower hμ (r.property.1.trans hu.1)) 2)
    simpa only [intervalIntegral.integral_const,smul_eq_mul] using hh
  calc
    _ = ((1-t)*β^2)*(((q:ℝ)-r)*s^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hI (mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg β))

theorem vectorDirectionDenominator_pos (μ : Paper.ParisiMeasure) (β t s : ℝ)
    (hβ : β≠0) (ht : t<1) (hs : 0<s) (hμ : μ∈scalarFloor s)
    (r q : Paper.Overlap) (hrq : r<q) :
    0<((1-t)*β^2)*∫u in (r:ℝ)..(q:ℝ),(Paper.parisiCDF μ u)^2 := by
  have hl := vectorDirectionDenominator_lower μ β t s ht.le hs.le hμ r q hrq.le
  have hp : 0<((1-t)*β^2)*s^2*((q:ℝ)-r) :=
    mul_pos (mul_pos (mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hβ)) (sq_pos_of_pos hs)) (sub_pos.mpr hrq)
  exact hp.trans_le hl

theorem vectorDirectionCovariance_decay_bounded (hn : 0<n)
    (μ : Paper.ParisiMeasure) (β t a : ℝ) (hβ : β≠0) (ht : t<1)
    (r q : Paper.Overlap) (hrq : r≤q)
    (b : VectorDisorderBrownianSample n→Field n)
    (hb : Measurable[vectorBrownianFiltration n (r:ℝ).toNNReal] b)
    (K : ℝ≥0) (hK : ∀sample,‖b sample‖≤K)
    (hden : 0<((1-t)*β^2)*∫u in (r:ℝ)..(q:ℝ),(Paper.parisiCDF μ u)^2) :
    vectorDirectionCovariance μ β t a ht.le b q≤
      (∫sample,‖b sample‖^2∂vectorMeasureDisorderTilt μ β t a)/
        (((1-t)*β^2)*∫u in (r:ℝ)..(q:ℝ),(Paper.parisiCDF μ u)^2) := by
  have := vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht.le
  let P := vectorMeasureDisorderTilt (n:=n) μ β t a
  let c := (1-t)*β^2
  let B := ∫sample,‖b sample‖^2∂P
  have hc : 0≤c := mul_nonneg (sub_nonneg.mpr ht.le) (sq_nonneg β)
  have hbm : Measurable b := hb.mono ((vectorBrownianFiltration n).le _) le_rfl
  have hb2 : MemLp b 2 P := MemLp.of_bound hbm.aestronglyMeasurable K (.of_forall hK)
  have hBn : 0≤B := integral_nonneg fun _=>sq_nonneg _
  by_cases hB : B=0
  · have hh := vectorDirectionCovariance_le_norm_moment μ β t a ht.le q b hb2
    change _≤2*(n:ℝ)^2*B at hh
    rw [hB,mul_zero] at hh
    change _≤B/(((1-t)*β^2)*∫u in (r:ℝ)..(q:ℝ),(Paper.parisiCDF μ u)^2)
    rw [hB,zero_div]
    exact hh
  have hBp : 0<B := lt_of_le_of_ne hBn (Ne.symm hB)
  let φ := fun u : ℝ=>vectorDirectionCovariance μ β t a ht.le b (projIcc 0 1 zero_le_one u)
  let f := fun u : ℝ=>c*vectorDirectionEnergy μ β t a ht.le b (projIcc 0 1 zero_le_one u)
  let g := fun u : ℝ=>c*(Paper.parisiCDF μ u)^2
  have hf : Continuous f :=
    ((continuous_vectorDirectionEnergy μ β t a ht.le b hbm K hK).comp continuous_projIcc).const_mul c
  have hg : IntervalIntegrable g volume (r:ℝ) q := by
    have hp : Monotone (fun u=>(Paper.parisiCDF μ u)^2) := fun x y hxy=>
      pow_le_pow_left₀ (Paper.parisiCDF_nonneg μ x) ((Paper.parisiCDF_monotone μ) hxy) 2
    exact hp.intervalIntegrable.const_mul c
  suffices hh : φ q≤B/(∫u in (r:ℝ)..(q:ℝ),g u) by
    simpa only [φ,g,B,P,c,projIcc_of_mem zero_le_one q.property,intervalIntegral.integral_const_mul] using hh
  apply integral_decay_riccati_bound (φ:=φ) (f:=f) (g:=g) hrq hBp (hf.intervalIntegrable _ _)
  · intro u _
    exact mul_nonneg hc (vectorDirectionEnergy_nonneg μ β t a ht.le b _)
  · intro u hu
    let v : Paper.Overlap := ⟨u,⟨r.property.1.trans hu.1,hu.2.trans q.property.2⟩⟩
    have hv : r≤v := hu.1
    simpa only [φ,f,v,projIcc_of_mem zero_le_one r.property,projIcc_of_mem zero_le_one v.property]
      using vectorDirectionCovariance_interval_evolution hn μ β t a hβ ht r v hv b hb K hK
  · intro u _
    exact vectorDirectionCovariance_nonneg μ β t a hβ ht b _
  · apply Filter.Eventually.of_forall
    intro u hu
    let v : Paper.Overlap := ⟨u,⟨r.property.1.trans hu.1,hu.2.trans q.property.2⟩⟩
    have hreact : (Paper.parisiCDF μ v)^2*(vectorDirectionCovariance μ β t a ht.le b v)^2≤
        B*vectorDirectionEnergy μ β t a ht.le b v :=
      vectorMeasure_averaged_random_reaction μ β t a hβ ht v b hb2
    have hh := mul_le_mul_of_nonneg_left hreact hc
    change c*(Paper.parisiCDF μ v)^2*(vectorDirectionCovariance μ β t a ht.le b (projIcc 0 1 zero_le_one u))^2≤B*(c*vectorDirectionEnergy μ β t a ht.le b (projIcc 0 1 zero_le_one u))
    have hv : projIcc 0 1 zero_le_one u=v := projIcc_of_mem zero_le_one v.property
    rw [hv]
    simpa only [mul_assoc,mul_left_comm,mul_comm] using hh
  · exact hg
  · simpa only [g,c,intervalIntegral.integral_const_mul] using hden

end QuantitativePaper
