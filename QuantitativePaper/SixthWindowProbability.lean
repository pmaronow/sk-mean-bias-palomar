module
public import QuantitativePaper.SixthWindowPaleyZygmund

@[expose] public section

/-! Genuine exponential upper and lower event estimates, before applying
the actual SK sixth-power moment window. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativePaper
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
set_option maxHeartbeats 1000000

theorem exponential_tilt_lower_tail (X : Ω → ℝ) (hXm : Measurable X)
    (s x : ℝ) (hs : 0 < s)
    (hi : Integrable (fun ω => Real.exp (s*X ω)) P)
    (hi2 : Integrable (fun ω => Real.exp ((2*s)*X ω)) P)
    (hx : s*x+Real.log 2 ≤ cgf X P s) :
    Real.exp (2*cgf X P s-cgf X P (2*s)-Real.log 4) ≤ P.real {ω | x ≤ X ω} := by
  let Z : Ω → ℝ := fun ω => Real.exp (s*X ω)
  have hZm : Measurable Z := Real.measurable_exp.comp (measurable_const.mul hXm)
  have hsquare : ∀ ω, Z ω^2=Real.exp ((2*s)*X ω) := by
    intro ω
    dsimp only [Z]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hZ : MemLp Z 2 P := (memLp_two_iff_integrable_sq hZm.aestronglyMeasurable).2
    (by simpa only [hsquare] using hi2)
  have hEZ : ∫ ω,Z ω ∂P=Real.exp (cgf X P s) := (exp_cgf hi).symm
  have hEZ2 : ∫ ω,Z ω^2 ∂P=Real.exp (cgf X P (2*s)) := by
    simp only [hsquare]
    exact (exp_cgf hi2).symm
  have hP := paley_zygmund_half Z hZm hZ (fun ω => (Real.exp_pos _).le)
    (by rw [hEZ2]; exact Real.exp_pos _)
  have hform : (∫ ω,Z ω ∂P)^2/(4*(∫ ω,Z ω^2 ∂P))=
      Real.exp (2*cgf X P s-cgf X P (2*s)-Real.log 4) := by
    rw [hEZ,hEZ2,Real.exp_sub,Real.exp_sub,Real.exp_log (by norm_num : (0:ℝ)<4)]
    have he : (Real.exp (cgf X P s))^2=Real.exp (2*cgf X P s) := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [he]
    ring
  rw [hform] at hP
  refine hP.trans (measureReal_mono ?_)
  intro ω hω
  change (∫ η,Z η ∂P)/2≤Z ω at hω
  have hz : Real.exp (s*x) ≤ Z ω := by
    have he : Real.exp (s*x) ≤ Real.exp (cgf X P s)/2 := by
      have hh := Real.exp_le_exp.mpr hx
      rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)] at hh
      linarith
    exact he.trans (by simpa only [hEZ] using hω)
  have hmul := Real.exp_le_exp.mp hz
  exact le_of_mul_le_mul_left hmul hs

theorem exponential_sixth_window_upper (X : Ω → ℝ) (s x N C : ℝ)
    (hs : 0 ≤ s) (hi : Integrable (fun ω => Real.exp (s*X ω)) P)
    (hwin : cgf X P s ≤ C*N*s^6) :
    P.real {ω | N*x ≤ X ω} ≤ Real.exp (N*(C*s^6-s*x)) := by
  have h := measure_ge_le_exp_cgf (X:=X) (μ:=P) (N*x) hs hi
  refine h.trans (Real.exp_le_exp.mpr ?_)
  nlinarith

theorem exponential_sixth_window_lower (X : Ω → ℝ) (hXm : Measurable X)
    (s x N a C : ℝ) (hs : 0<s) (hN : 0≤N)
    (hi : Integrable (fun ω => Real.exp (s*X ω)) P)
    (hi2 : Integrable (fun ω => Real.exp ((2*s)*X ω)) P)
    (hlower : a*N*s^6 ≤ cgf X P s)
    (hupper : cgf X P (2*s) ≤ C*N*(2*s)^6)
    (hsize : Real.log 4 ≤ a*N*s^6)
    (hx : s*(N*x)+Real.log 2 ≤ a*N*s^6) :
    Real.exp (-(64*C+a)*N*s^6) ≤ P.real {ω | N*x ≤ X ω} := by
  have h := exponential_tilt_lower_tail X hXm s (N*x) hs hi hi2 (hx.trans hlower)
  refine le_trans (Real.exp_le_exp.mpr ?_) h
  have hpos : 0≤a*N*s^6 := (Real.log_nonneg (by norm_num : (1:ℝ)≤4)).trans hsize
  nlinarith [show C*N*(2*s)^6=64*C*N*s^6 by ring]

end QuantitativePaper
