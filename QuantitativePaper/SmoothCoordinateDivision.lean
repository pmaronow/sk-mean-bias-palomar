module
public import QuantitativePaper.CompactSmoothIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-! A smooth coordinate quotient at its genuine removable value.
The exact value and all parameter smoothness follow from the fundamental
theorem of calculus on a compact interval, including coordinate zero. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace QuantitativePaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

def smoothCoordinateSlope (f : ℝ×E→ℝ) (z : ℝ×E) : ℝ :=
  if z.1=0 then fderiv ℝ f (0,z.2) (1,0) else f z/z.1

def smoothCoordinateSlopeIntegral (f : ℝ×E→ℝ) (z : ℝ×E) : ℝ :=
  ∫r in Icc (0:ℝ) 1, fderiv ℝ f (r*z.1,z.2) (1,0)

theorem smoothCoordinateSlope_eq_integral (f : ℝ×E→ℝ) (hf : ContDiff ℝ ∞ f)
    (hzero : ∀x, f (0,x)=0) (z : ℝ×E) :
    smoothCoordinateSlope f z=smoothCoordinateSlopeIntegral f z := by
  unfold smoothCoordinateSlope smoothCoordinateSlopeIntegral
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (show (0:ℝ)≤1 by norm_num)]
  by_cases hz : z.1=0
  · simp only [hz,ite_true,mul_zero]
    simp only [intervalIntegral.integral_const,sub_zero,one_smul]
  · rw [if_neg hz]
    let D : ℝ→ℝ := fun r=>fderiv ℝ f (r*z.1,z.2) (1,0)
    have hc : Continuous D := (hf.continuous_fderiv (by simp)).comp
      ((continuous_id.mul continuous_const).prodMk continuous_const) |>.clm_apply continuous_const
    have hd (r : ℝ) : HasDerivAt (fun t=>f (t*z.1,z.2)) (z.1*D r) r := by
      have hh := (hf.differentiable (by simp) (r*z.1,z.2)).hasFDerivAt.comp_hasDerivAt r
        (((hasDerivAt_id r).mul_const z.1).prodMk (hasDerivAt_const r z.2))
      apply hh.congr_deriv
      simp only [one_mul]
      change fderiv ℝ f (r*z.1,z.2) (z.1,0)=z.1*D r
      have he : (z.1,(0:E))=z.1 • ((1:ℝ),(0:E)) := by simp
      rw [he,map_smul]
      rfl
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r _=>hd r) ((hc.const_mul z.1).intervalIntegrable 0 1)
    simp only [one_mul,zero_mul,hzero,sub_zero,intervalIntegral.integral_const_mul] at hFTC
    change f z/z.1=∫r in (0:ℝ)..1,D r
    apply (div_eq_iff hz).mpr
    simpa only [mul_comm] using hFTC.symm

theorem contDiff_smoothCoordinateSlopeIntegral (f : ℝ×E→ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (smoothCoordinateSlopeIntegral f) := by
  let G : ℝ×(ℝ×E)→ℝ := fun w=>fderiv ℝ f (w.1*w.2.1,w.2.2) (1,0)
  have hfd : ContDiff ℝ ∞ (fderiv ℝ f) := (contDiff_infty_iff_fderiv.mp hf).2
  have hG : ContDiff ℝ ∞ G := (hfd.comp (by fun_prop)).clm_apply contDiff_const
  exact contDiff_compact_parameter_integral G hG 0 1

theorem contDiff_smoothCoordinateSlope (f : ℝ×E→ℝ) (hf : ContDiff ℝ ∞ f)
    (hzero : ∀x, f (0,x)=0) : ContDiff ℝ ∞ (smoothCoordinateSlope f) := by
  have he := funext (smoothCoordinateSlope_eq_integral f hf hzero)
  rw [he]
  exact contDiff_smoothCoordinateSlopeIntegral f hf

end QuantitativePaper
