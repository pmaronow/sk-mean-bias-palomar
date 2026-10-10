module
public import QuantitativePaper.SixthWindowConsequences
public import QuantitativeFollowup.ImprovedWindowScalePowers

@[expose] public section

/-! Genuine matching six-fifths tails from the improved seventh-fiftieth
sixth-power tilt window, retaining the actual event and measure. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper
namespace QuantitativeFollowup
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
set_option maxHeartbeats 1800000

theorem improved_lower_sixth_tilt_cutoff (a A N x : ℝ) (ha : 0<a) (hA : 0≤A)
    (hN : 0<N) (hx : 0<x) (hbound : a/2*A^5*N^(-(7/10:ℝ))≤x) :
    A*N^(-(7/50:ℝ))≤(2*x/a)^(1/5:ℝ) := by
  have hs0 : 0≤(2*x/a)^(1/5:ℝ) := Real.rpow_nonneg (by positivity) _
  apply le_of_pow_le_pow_left₀ (by norm_num : (5:ℕ)≠0) hs0
  rw [fifthRoot_pow_five (by positivity : 0≤2*x/a),mul_pow,
    ←Real.rpow_mul_natCast hN.le]
  norm_num
  apply (le_div_iff₀ ha).2
  nlinarith

theorem improved_lower_sixth_tilt_size (a A N s : ℝ) (ha : 0≤a) (hA : 0≤A)
    (hN : 0<N) (hs : A*N^(-(7/50:ℝ))≤s) :
    a*A^6*N^(4/25:ℝ)≤a*N*s^6 := by
  have hp := pow_le_pow_left₀ (by positivity : 0≤A*N^(-(7/50:ℝ))) hs 6
  have he : N*(A*N^(-(7/50:ℝ)))^6=A^6*N^(4/25:ℝ) := by
    rw [mul_pow,←Real.rpow_mul_natCast hN.le]
    norm_num
    have hr : N*N^(-(21/25:ℝ))=N^(4/25:ℝ) := by
      calc
        _=N^(1:ℝ)*N^(-(21/25:ℝ)) := by rw [Real.rpow_one]
        _=N^(4/25:ℝ) := by rw [←Real.rpow_add hN];norm_num
    calc
      _=A^6*(N*N^(-(21/25:ℝ))) := by ring
      _=_ := by rw [hr]
  have hh := mul_le_mul_of_nonneg_left hp (mul_nonneg ha hN.le)
  nlinarith [he]


theorem improved_sixth_window_probability_bounds (X : Ω → ℝ) (hXm : Measurable X)
    (N a C A L x : ℝ) (hN : 0<N) (ha : 0<a) (hC : 0<C) (haC : a≤C)
    (hA : 0<A) (hL : 0<L)
    (hi : ∀ s : ℝ,0<s→s≤L→Integrable (fun ω => Real.exp (s*X ω)) P)
    (hupper : ∀ s : ℝ,0<s→s≤L→cgf X P s≤C*N*s^6)
    (hlower : ∀ s : ℝ,A*N^(-(7/50:ℝ))≤s→s≤L→a*N*s^6≤cgf X P s)
    (hsize : Real.log 4≤a*A^6*N^(4/25:ℝ))
    (hxlow : a/2*A^5*N^(-(7/10:ℝ))≤x)
    (hxhigh : x≤a/2*(L/2)^5) :
    Real.exp (-((64*C+a)*(2/a)^(6/5:ℝ))*N*x^(6/5:ℝ))≤P.real {ω | N*x≤X ω} ∧
      P.real {ω | N*x≤X ω}≤Real.exp (-(5/(6*(6*C)^(1/5:ℝ)))*N*x^(6/5:ℝ)) := by
  have hx : 0<x := (show 0<a/2*A^5*N^(-(7/10:ℝ)) by positivity).trans_le hxlow
  let slo := (2*x/a)^(1/5:ℝ)
  have hslo := lower_sixth_tilt_mem a x L ha hx hL hxhigh
  have hcut := improved_lower_sixth_tilt_cutoff a A N x ha hA.le hN hx hxlow
  have hsloL : slo≤L := hslo.2.trans (by linarith)
  have helo := lower_sixth_tilt_identity a x ha hx
  have htimes : Real.log 4≤a*N*slo^6 := hsize.trans
    (improved_lower_sixth_tilt_size a A N slo ha.le hA.le hN hcut)
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


end QuantitativeFollowup
