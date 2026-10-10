module
public import QuantitativePaper.ScalarLogSecondDerivative

@[expose] public section

/-! Exact third derivatives of an actual scalar exponential and positive
partition. These are ordinary derivatives on the stated open domain. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativePaper
set_option maxHeartbeats 1200000

theorem iteratedDeriv_three_exp_mul_on_open (f : ℝ→ℝ) (a : ℝ) (U : Set ℝ)
    (hU : IsOpen U) (hf : ContDiffOn ℝ 3 f U) {x : ℝ} (hx : x∈U) :
    iteratedDeriv 3 (fun y=>Real.exp (a*f y)) x=
      Real.exp (a*f x)*(a*iteratedDeriv 3 f x+
        3*a^2*deriv f x*iteratedDeriv 2 f x+a^3*(deriv f x)^3) := by
  have hs:=(hf x hx).contDiffAt (hU.mem_nhds hx)
  have hd:=(hs.differentiableAt (by norm_num)).hasDerivAt
  have hs1 : ContDiffAt ℝ 2 (deriv f) x:=hs.derivWithin (by norm_num)
  have hd1:=(hs1.differentiableAt (by norm_num)).hasDerivAt
  have hd2:=((hs1.derivWithin (by norm_num) : ContDiffAt ℝ 1 (deriv (deriv f)) x).differentiableAt
    (by norm_num)).hasDerivAt
  have he : deriv (deriv (fun y=>Real.exp (a*f y)))=ᶠ[𝓝 x]
      (fun y=>Real.exp (a*f y)*(a*deriv (deriv f) y+a^2*(deriv f y)^2)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
      iteratedDeriv_two_exp_mul_on_open f a U hU (hf.of_le (by norm_num)) hy
  have hh:=((hd.const_mul a).exp.mul
    ((hd2.const_mul a).add ((hd1.pow 2).const_mul (a^2)))).congr_of_eventuallyEq he
  simp only [iteratedDeriv_succ,iteratedDeriv_zero]
  rw [hh.deriv]
  norm_num only [Pi.add_apply,Pi.pow_apply,Nat.reduceSub,Nat.cast_ofNat,pow_one]
  ring

theorem iteratedDeriv_three_log_on_open (f : ℝ→ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 3 f U) (hpos : ∀x∈U,0<f x) {x : ℝ} (hx : x∈U) :
    iteratedDeriv 3 (fun y=>Real.log (f y)) x=
      iteratedDeriv 3 f x/f x-3*deriv f x*iteratedDeriv 2 f x/(f x)^2+
        2*(deriv f x/f x)^3 := by
  have hs:=(hf x hx).contDiffAt (hU.mem_nhds hx)
  have hd:=(hs.differentiableAt (by norm_num)).hasDerivAt
  have hs1 : ContDiffAt ℝ 2 (deriv f) x:=hs.derivWithin (by norm_num)
  have hd1:=(hs1.differentiableAt (by norm_num)).hasDerivAt
  have hd2:=((hs1.derivWithin (by norm_num) : ContDiffAt ℝ 1 (deriv (deriv f)) x).differentiableAt
    (by norm_num)).hasDerivAt
  have he : deriv (deriv (fun y=>Real.log (f y)))=ᶠ[𝓝 x]
      (fun y=>deriv (deriv f) y/f y-(deriv f y/f y)^2) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (hasDerivAt_deriv_log_on_open f U hU (hf.of_le (by norm_num)) hpos hy).deriv
  have hh:=((hd2.div hd (hpos x hx).ne').sub
    ((hd1.div hd (hpos x hx).ne').pow 2)).congr_of_eventuallyEq he
  simp only [iteratedDeriv_succ,iteratedDeriv_zero]
  rw [hh.deriv]
  norm_num only [Pi.div_apply,Nat.reduceSub,Nat.cast_ofNat,pow_one]
  field_simp [(hpos x hx).ne']
  <;>ring

end QuantitativePaper
