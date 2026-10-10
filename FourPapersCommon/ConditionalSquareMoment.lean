module
public import FourPapersCommon.WeightedConditionalIntegral
public import Mathlib.Probability.CondVar

@[expose] public section

/-! Exact square expansion and conditional pull-out for an L² known offset. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {P : Measure Ω}

theorem integral_condExp_sub_known_sq [IsFiniteMeasure P]
    (m : MeasurableSpace Ω) (hm : m≤m₀) (F Z : Ω→ℝ)
    (hF : MemLp F 2 P) (hZ : MemLp Z 2 P) (hknown : StronglyMeasurable[m] Z) :
    (∫x,(P[F|m] x-Z x)^2∂P)=
      (∫x,(P[F|m] x)^2∂P)-2*(∫x,F x*Z x∂P)+(∫x,(Z x)^2∂P) := by
  letI : MeasurableSpace Ω:=m₀
  have hCE:=hF.condExp one_le_two (m:=m)
  have hCZ : Integrable (fun x=>P[F|m] x*Z x) P:=hCE.integrable_mul hZ
  have hZF : Integrable (fun x=>Z x*F x) P:=hZ.integrable_mul hF
  have hp:=integral_known_mul_condExp m hm Z F hknown
    (hF.integrable one_le_two) hZF
  have he : (fun x=>(P[F|m] x-Z x)^2)=
      fun x=>(P[F|m] x)^2-2*(P[F|m] x*Z x)+(Z x)^2 := by
    funext x
    ring
  rw [he]
  have hadd:=integral_add (hCE.integrable_sq.sub (hCZ.const_mul 2)) hZ.integrable_sq
  have hsub:=integral_sub hCE.integrable_sq (hCZ.const_mul 2)
  simp only [Pi.add_apply,Pi.sub_apply] at hadd hsub
  rw [hadd,hsub,integral_const_mul]
  have hp' : (∫x,P[F|m] x*Z x∂P)=∫x,F x*Z x∂P := by
    simpa only [mul_comm] using hp
  rw [hp']

end FourPapersCommon
