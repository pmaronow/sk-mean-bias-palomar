module
public import QuantitativePaper.VectorFiniteMeasureDriftStability
public import QuantitativePaper.VectorAdditiveStability

@[expose] public section

/-! Genuine same-driver finite-to-arbitrary-profile state comparison using
the proved CDF L1 envelope and actual Picard stability. -/
noncomputable section
open Set MeasureTheory FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
variable {n k : ℕ}
set_option maxHeartbeats 400000

theorem norm_vectorMeasureState_sub_finite_le (μ : Paper.ParisiMeasure) (s : SpinGlass.Targets.RSBScheme k) (β t : ℝ) (ht : t≤1)
    (D : ℝ) (hD : 0≤D)
    (hgrad : ∀ q p x,‖vectorMeasureGradient (n := n) μ β t q p x-
      vectorFiniteTailGradient s β t q p x‖≤D)
    (r : ℝ≥0) (hr : r≤1) (sample : VectorDisorderBrownianSample n) :
    ‖vectorMeasureState (n := n) μ β t ht r sample-vectorFiniteState (n := n) s β t ht r sample‖≤
      (((1-t)*β^2)*Real.exp (((1-t)*β^2)*(n : ℝ)))*
        (Real.sqrt n*Paper.parisiCDFDistance μ (Paper.parisiSchemeMeasure s)+D) := by
  let c:ℝ:=(1-t)*β^2
  let a:ℝ→ℝ:=fun u=>c*(Real.sqrt n*|Paper.parisiCDF μ u-Paper.parisiCDF (Paper.parisiSchemeMeasure s) u|+D)
  have hc : 0≤c := mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg _)
  have ha : IntervalIntegrable a volume 0 1 :=
    (((Paper.parisiCDF_abs_diff_intervalIntegrable μ (Paper.parisiSchemeMeasure s) 0 1).const_mul (Real.sqrt n)).add
      intervalIntegrable_const).const_mul c
  have ha0 : ∀s∈Icc (0 : ℝ) 1,0≤a s := by
    intro s _
    exact mul_nonneg hc (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) hD)
  have hpert : ∀u : ℝ≥0,u≤1→∀p x,
      ‖(vectorMeasureDriftData (n := n) μ β t ht).drift u p x-
        (vectorFiniteDriftData (n := n) s β t ht).drift u p x‖≤a u := by
    intro u _ p x
    exact norm_vectorMeasureFiniteDrift_sub_le μ s β t ht D hD hgrad u p x
  have hh:=norm_vectorAdditiveState_sub_le_of_L1Drift
    (vectorMeasureDriftData (n := n) μ β t ht) (vectorFiniteDriftData (n := n) s β t ht)
    (Real.sqrt c) 0 1 a ha ha0 hpert r hr sample
  change ‖vectorMeasureState (n := n) μ β t ht r sample-
    vectorFiniteState (n := n) s β t ht r sample‖≤
      (∫s in (0 : ℝ)..1,a s)*Real.exp (c*(n : ℝ)*r) at hh
  have hi : (∫s in (0 : ℝ)..1,a s)=c*(Real.sqrt n*Paper.parisiCDFDistance μ (Paper.parisiSchemeMeasure s)+D) :=
    vectorMeasureDrift_envelope_integral μ (Paper.parisiSchemeMeasure s) β t D
  rw [hi] at hh
  have he : Real.exp (c*(n : ℝ)*r)≤Real.exp (c*(n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_of_le_one_right (mul_nonneg hc (Nat.cast_nonneg _)) (by exact_mod_cast hr)
  have hE : 0≤c*(Real.sqrt n*Paper.parisiCDFDistance μ (Paper.parisiSchemeMeasure s)+D) :=
    mul_nonneg hc (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Paper.parisiCDFDistance_nonneg μ (Paper.parisiSchemeMeasure s))) hD)
  convert hh.trans (mul_le_mul_of_nonneg_left he hE) using 1 <;> ring

end QuantitativePaper
