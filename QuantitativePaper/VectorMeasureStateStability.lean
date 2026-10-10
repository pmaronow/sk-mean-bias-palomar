module
public import QuantitativePaper.VectorMeasureDriftStability
public import QuantitativePaper.VectorAdditiveStability

@[expose] public section

/-! Same-driver stability of the actual arbitrary-profile vector diffusion.
CDF jumps are controlled in L¹; the measurable drift is never differentiated. -/
noncomputable section
open Set MeasureTheory FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 400000

theorem norm_vectorMeasureState_sub_le (μ ν : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (D : ℝ) (hD : 0≤D)
    (hgrad : ∀ q p x,‖vectorMeasureGradient (n := n) μ β t q p x-
      vectorMeasureGradient ν β t q p x‖≤D)
    (r : ℝ≥0) (hr : r≤1) (sample : VectorDisorderBrownianSample n) :
    ‖vectorMeasureState (n := n) μ β t ht r sample-vectorMeasureState (n := n) ν β t ht r sample‖≤
      (((1-t)*β^2)*Real.exp (((1-t)*β^2)*(n : ℝ)))*
        (Real.sqrt n*Paper.parisiCDFDistance μ ν+D) := by
  let c:ℝ:=(1-t)*β^2
  let a:ℝ→ℝ:=fun s=>c*(Real.sqrt n*|Paper.parisiCDF μ s-Paper.parisiCDF ν s|+D)
  have hc : 0≤c := mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg _)
  have ha : IntervalIntegrable a volume 0 1 :=
    (((Paper.parisiCDF_abs_diff_intervalIntegrable μ ν 0 1).const_mul (Real.sqrt n)).add
      intervalIntegrable_const).const_mul c
  have ha0 : ∀s∈Icc (0 : ℝ) 1,0≤a s := by
    intro s _
    exact mul_nonneg hc (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) hD)
  have hpert : ∀u : ℝ≥0,u≤1→∀p x,
      ‖(vectorMeasureDriftData (n := n) μ β t ht).drift u p x-
        (vectorMeasureDriftData (n := n) ν β t ht).drift u p x‖≤a u := by
    intro u _ p x
    exact norm_vectorMeasureDrift_sub_le μ ν β t ht D hD hgrad u p x
  have hh:=norm_vectorAdditiveState_sub_le_of_L1Drift
    (vectorMeasureDriftData (n := n) μ β t ht) (vectorMeasureDriftData (n := n) ν β t ht)
    (Real.sqrt c) 0 1 a ha ha0 hpert r hr sample
  change ‖vectorMeasureState (n := n) μ β t ht r sample-
    vectorMeasureState (n := n) ν β t ht r sample‖≤
      (∫s in (0 : ℝ)..1,a s)*Real.exp (c*(n : ℝ)*r) at hh
  have hi : (∫s in (0 : ℝ)..1,a s)=c*(Real.sqrt n*Paper.parisiCDFDistance μ ν+D) :=
    vectorMeasureDrift_envelope_integral μ ν β t D
  rw [hi] at hh
  have he : Real.exp (c*(n : ℝ)*r)≤Real.exp (c*(n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_of_le_one_right (mul_nonneg hc (Nat.cast_nonneg _)) (by exact_mod_cast hr)
  have hE : 0≤c*(Real.sqrt n*Paper.parisiCDFDistance μ ν+D) :=
    mul_nonneg hc (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Paper.parisiCDFDistance_nonneg μ ν)) hD)
  convert hh.trans (mul_le_mul_of_nonneg_left he hE) using 1 <;> ring

end QuantitativePaper
