module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

/-! The scalar second-moment increment identity, separated from large
constructed stochastic functions to keep integral elaboration local. -/
noncomputable section
open MeasureTheory
namespace FourPapersCommon
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f g : Ω→ℝ}

theorem integrable_square_sub (hf : Integrable (fun ω=>f ω^2) P)
    (hg : Integrable (fun ω=>g ω^2) P) (hgf : Integrable (fun ω=>g ω*f ω) P) :
    Integrable (fun ω=>(f ω-g ω)^2) P := by
  convert (hf.add hg).sub (hgf.const_mul 2) using 1
  funext ω
  simp only [Pi.sub_apply,Pi.add_apply]
  ring

theorem integral_square_sub_of_cross (hf : Integrable (fun ω=>f ω^2) P)
    (hg : Integrable (fun ω=>g ω^2) P) (hgf : Integrable (fun ω=>g ω*f ω) P)
    (hc : (∫ω,g ω*f ω∂P)=∫ω,g ω^2∂P) :
    (∫ω,(f ω-g ω)^2∂P)=(∫ω,f ω^2∂P)-(∫ω,g ω^2∂P) := by
  have he : (fun ω=>(f ω-g ω)^2)=
      ((fun ω=>f ω^2)+(fun ω=>g ω^2))-(fun ω=>2*(g ω*f ω)) := by
    funext ω
    simp only [Pi.sub_apply,Pi.add_apply]
    ring
  rw [he]
  change (∫ω,f ω^2+g ω^2-2*(g ω*f ω)∂P)=_
  have hdiff : (∫ω,f ω^2+g ω^2-2*(g ω*f ω)∂P)=
      (∫ω,f ω^2+g ω^2∂P)-(∫ω,2*(g ω*f ω)∂P) :=
    integral_sub (hf.add hg) (hgf.const_mul 2)
  have hsum : (∫ω,f ω^2+g ω^2∂P)=(∫ω,f ω^2∂P)+(∫ω,g ω^2∂P):=
    integral_add hf hg
  rw [hdiff,hsum,integral_const_mul,hc]
  ring

end FourPapersCommon
