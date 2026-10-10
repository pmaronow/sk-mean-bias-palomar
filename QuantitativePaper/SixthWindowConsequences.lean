module
public import QuantitativePaper.SixthWindowTiltCalculus

@[expose] public section

/-! Conversion of a genuine sixth-power cumulant window to matching
six-fifths upper-tail probabilities. Model moment estimates are applied
separately; this theorem assumes no tail estimate. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativePaper
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
set_option maxHeartbeats 1000000

theorem sixth_window_probability_bounds (X : Ω → ℝ) (hXm : Measurable X)
    (N a C A L x : ℝ) (hN : 0<N) (ha : 0<a) (hC : 0<C) (haC : a≤C)
    (hA : 0<A) (hL : 0<L)
    (hi : ∀ s : ℝ,0<s→s≤L→Integrable (fun ω => Real.exp (s*X ω)) P)
    (hupper : ∀ s : ℝ,0<s→s≤L→cgf X P s≤C*N*s^6)
    (hlower : ∀ s : ℝ,A*N^(-(2/15:ℝ))≤s→s≤L→a*N*s^6≤cgf X P s)
    (hsize : Real.log 4≤a*A^6*N^(1/5:ℝ))
    (hxlow : a/2*A^5*N^(-(2/3:ℝ))≤x)
    (hxhigh : x≤a/2*(L/2)^5) :
    Real.exp (-((64*C+a)*(2/a)^(6/5:ℝ))*N*x^(6/5:ℝ))≤P.real {ω | N*x≤X ω} ∧
      P.real {ω | N*x≤X ω}≤Real.exp (-(5/(6*(6*C)^(1/5:ℝ)))*N*x^(6/5:ℝ)) := by
  have hx : 0<x := (show 0<a/2*A^5*N^(-(2/3:ℝ)) by positivity).trans_le hxlow
  let slo := (2*x/a)^(1/5:ℝ)
  have hslo := lower_sixth_tilt_mem a x L ha hx hL hxhigh
  have hcut := lower_sixth_tilt_cutoff a A N x ha hA.le hN hx hxlow
  have hsloL : slo≤L := hslo.2.trans (by linarith)
  have helo := lower_sixth_tilt_identity a x ha hx
  have htimes : Real.log 4≤a*N*slo^6 := hsize.trans
    (lower_sixth_tilt_size a A N slo ha.le hA.le hN hcut)
  have hxmul : slo*(N*x)+Real.log 2≤a*N*slo^6 := by
    have he : a*N*slo^6=2*slo*(N*x) := by
      have hh : slo^5=2*x/a := helo.1
      have hz : slo^6=slo*slo^5 := by ring
      rw [hz,hh]
      field_simp
    have hlog : Real.log 4=2*Real.log 2 := by
      rw [show (4:ℝ)=2*2 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
      ring
    rw [hlog] at htimes
    linarith
  have hlow := exponential_sixth_window_lower X hXm slo x N a C hslo.1 hN.le
    (hi slo hslo.1 hsloL) (hi (2*slo) (by linarith [hslo.1]) (by linarith [hslo.2]))
    (hlower slo hcut hsloL) (hupper (2*slo) (by linarith [hslo.1]) (by linarith [hslo.2]))
    htimes hxmul
  have hlowFinal : Real.exp (-((64*C+a)*(2/a)^(6/5:ℝ))*N*x^(6/5:ℝ))≤
      P.real {ω | N*x≤X ω} := by
    convert hlow using 1
    congr 1
    rw [helo.2]
    ring
  let sup := x^(1/5:ℝ)/(6*C)^(1/5:ℝ)
  have hxupper : x≤6*C*L^5 := by
    have hh : (L/2)^5≤L^5 := pow_le_pow_left₀ (by positivity) (by linarith) 5
    have hp := mul_le_mul_of_nonneg_left hh (show 0≤a/2 by positivity)
    have hq : a/2*L^5≤6*C*L^5 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    exact hxhigh.trans (hp.trans hq)
  have hsup := upper_sixth_tilt_mem C x L hC hx hL hxupper
  have hup := exponential_sixth_window_upper X sup x N C hsup.1.le
    (hi sup hsup.1 hsup.2) (hupper sup hsup.1 hsup.2)
  refine ⟨hlowFinal,?_⟩
  convert hup using 1
  congr 1
  rw [upper_sixth_tilt_identity C x hC hx]
  ring

end QuantitativePaper
