module
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-! The exact square estimate underlying the quantile-bin argument. -/
noncomputable section
open Set MeasureTheory
namespace FourPapersCommon
set_option maxHeartbeats 800000

theorem square_le_of_two_sided_comparison (x yp ym d : ℝ) (hd : 0≤d)
    (hp : x≤d+2*yp) (hm : -d+2*ym≤x) :
    x^2≤2*d^2+8*yp^2+8*ym^2 := by
  by_cases hx : 0≤x
  · have hprod:=mul_nonneg (show 0≤d+2*yp-x by linarith)
      (show 0≤d+2*yp+x by linarith)
    nlinarith [sq_nonneg (d-2*yp),sq_nonneg ym]
  · have hprod:=mul_nonneg (show 0≤d-2*ym+x by linarith)
      (show 0≤d-2*ym-x by linarith)
    nlinarith [sq_nonneg (d+2*ym),sq_nonneg yp]

theorem integral_square_le_of_two_sided_comparison {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Yp Ym : Ω→ℝ)
    (hX : MemLp X 2 P) (hYp : MemLp Yp 2 P) (hYm : MemLp Ym 2 P)
    (d : ℝ) (hd : 0≤d) (hp : X≤ᵐ[P]fun ω=>d+2*Yp ω)
    (hm : (fun ω=>-d+2*Ym ω)≤ᵐ[P]X) :
    (∫ω,X ω^2 ∂P)≤2*d^2+8*(∫ω,Yp ω^2 ∂P)+8*(∫ω,Ym ω^2 ∂P) := by
  have h:=integral_mono_ae hX.integrable_sq
    (((integrable_const (2*d^2)).add (hYp.integrable_sq.const_mul 8)).add
      (hYm.integrable_sq.const_mul 8)) (show
    (fun ω=>X ω^2)≤ᵐ[P]fun ω=>2*d^2+8*Yp ω^2+8*Ym ω^2 from by
      filter_upwards [hp,hm] with ω hpω hmω
      exact square_le_of_two_sided_comparison _ _ _ d hd hpω hmω)
  have he1:=integral_add (integrable_const (2*d^2)) (hYp.integrable_sq.const_mul 8)
  have he2:=integral_add ((integrable_const (2*d^2)).add (hYp.integrable_sq.const_mul 8))
    (hYm.integrable_sq.const_mul 8)
  simp only [Pi.add_apply] at h he1 he2
  rw [he2,he1] at h
  simpa only [integral_const_mul,integral_const,probReal_univ,one_smul] using h

end FourPapersCommon
