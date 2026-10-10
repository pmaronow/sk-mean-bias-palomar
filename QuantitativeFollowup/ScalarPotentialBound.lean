module
public import QuantitativeFollowup.ScalarSourceBounds
public import Paper.ParisiPotentialStability

@[expose] public section

/-! A genuine uniform bound on the actual scalar potential difference on
the physical strip, needed for closed-endpoint Itô passage. -/
noncomputable section
open Set MeasureTheory Paper FRSB
namespace QuantitativeFollowup

theorem norm_parisiPotential_sub_le (β : ℝ) (μ ν : Paper.ParisiMeasure)
    (t x : ℝ) (ht : t∈Icc (0:ℝ) 1) :
    ‖parisiPotential β μ (t,x)-parisiPotential β ν (t,x)‖≤(5/2:ℝ)*β^2 := by
  rw [parisiPotential_eq_duhamel β μ t x ht.2,parisiPotential_eq_duhamel β ν t x ht.2]
  have h:=norm_parisiDuhamelPotential_measure_gradient_sub_le β μ ν
    (parisiGradient β μ) (parisiGradient β ν)
    (continuous_parisiGradient β μ).measurable (continuous_parisiGradient β ν).measurable
    1 2 (norm_parisiGradient_le_one β μ) (norm_parisiGradient_le_one β ν)
    (fun p=>(norm_sub_le _ _).trans (by linarith [norm_parisiGradient_le_one β μ p, norm_parisiGradient_le_one β ν p])) t x ht
  have hi : (∫s in (0:ℝ)..1,‖parisiCDF μ s-parisiCDF ν s‖)≤1 := by
    have hh:=intervalIntegral.integral_mono_on (a:=(0:ℝ)) (b:=1) zero_le_one
      (((parisiCDF_intervalIntegrable μ 0 1).sub (parisiCDF_intervalIntegrable ν 0 1)).norm)
      (intervalIntegrable_const (c:=(1:ℝ))) (fun s _=>norm_parisiCDF_sub_le_one μ ν s)
    simpa using hh
  nlinarith [mul_le_mul_of_nonneg_left hi (by positivity : (0:ℝ)≤β^2/2)]

end QuantitativeFollowup
