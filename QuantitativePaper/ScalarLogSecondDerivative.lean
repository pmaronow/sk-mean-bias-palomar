module
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section

/-! Exact ordinary second derivatives of a positive actual partition. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativePaper
set_option maxHeartbeats 900000

theorem hasDerivAt_deriv_log_on_open (f : ℝ→ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) (hpos : ∀x∈U,0<f x) {x : ℝ} (hx : x∈U) :
    HasDerivAt (deriv (fun y=>Real.log (f y)))
      (deriv (deriv f) x/f x-(deriv f x/f x)^2) x := by
  have hs:=(hf x hx).contDiffAt (hU.mem_nhds hx)
  have hd:=(hs.differentiableAt (by norm_num)).hasDerivAt
  have hs' : ContDiffAt ℝ 1 (deriv f) x:=hs.derivWithin (by norm_num)
  have hd':=(hs'.differentiableAt (by norm_num)).hasDerivAt
  have he : deriv (fun y=>Real.log (f y))=ᶠ[𝓝 x](fun y=>deriv f y/f y):=by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (((hf y hy).contDiffAt (hU.mem_nhds hy)).differentiableAt
      (by norm_num)).hasDerivAt.log (hpos y hy).ne' |>.deriv
  have hh:=hd'.div hd (hpos x hx).ne'
  convert hh.congr_of_eventuallyEq he using 1
  field_simp [(hpos x hx).ne']

theorem iteratedDeriv_two_log_on_open (f : ℝ→ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) (hpos : ∀x∈U,0<f x) {x : ℝ} (hx : x∈U) :
    iteratedDeriv 2 (fun y=>Real.log (f y)) x=
      iteratedDeriv 2 f x/f x-(deriv f x/f x)^2 := by
  simpa only [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero,iteratedDeriv_one]
    using (hasDerivAt_deriv_log_on_open f U hU hf hpos hx).deriv

theorem iteratedDeriv_two_exp_mul_on_open (f : ℝ→ℝ) (a : ℝ) (U : Set ℝ)
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) {x : ℝ} (hx : x∈U) :
    iteratedDeriv 2 (fun y=>Real.exp (a*f y)) x=
      Real.exp (a*f x)*(a*iteratedDeriv 2 f x+a^2*(deriv f x)^2) := by
  have hs:=(hf x hx).contDiffAt (hU.mem_nhds hx)
  have hd:=(hs.differentiableAt (by norm_num)).hasDerivAt
  have hs' : ContDiffAt ℝ 1 (deriv f) x:=hs.derivWithin (by norm_num)
  have hd':=(hs'.differentiableAt (by norm_num)).hasDerivAt
  have he : deriv (fun y=>Real.exp (a*f y))=ᶠ[𝓝 x]
      (fun y=>Real.exp (a*f y)*(a*deriv f y)):=by
    filter_upwards [hU.mem_nhds hx] with y hy
    have hdy:=(((hf y hy).contDiffAt (hU.mem_nhds hy)).differentiableAt
      (by norm_num)).hasDerivAt
    exact (hdy.const_mul a).exp.deriv
  have hh:=((hd.const_mul a).exp.mul (hd'.const_mul a)).congr_of_eventuallyEq he
  have heq:=hh.deriv
  rw [show iteratedDeriv 2 (fun y=>Real.exp (a*f y)) x=
      deriv (deriv (fun y=>Real.exp (a*f y))) x by
    rw [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one]]
  rw [heq]
  simp only [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero,iteratedDeriv_one]
  ring

end QuantitativePaper
