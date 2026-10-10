module
public import OverlapPaper.ReplicaSourceBranchingEstimate
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

@[expose] public section

/-! A bounded full-past pairing identifies a genuine conditional expectation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace FourPapersCommon
open OverlapPaper
variable {Ω : Type*}

theorem condExp_of_bounded_past_pairings (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ mΩ) (f g : Ω→ℝ) (hf : Measurable f)
    (hg : StronglyMeasurable[m] g) (C : ℝ) (hfC : ∀x,|f x|≤C) (hgC : ∀x,|g x|≤C)
    (hpair : ∀Z : Ω→ℝ,Measurable[m] Z→(∀x,‖Z x‖≤1)→
      (∫x,Z x*f x∂P)=∫x,Z x*g x∂P) :
    P[f|m]=ᵐ[P] g := by
  letI : MeasurableSpace Ω:=mΩ
  have hfi:=source_bounded_integrable P f hf C hfC
  have hgi:=source_bounded_integrable P g (hg.mono hm).measurable C hgC
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hfi
  · intro A _ _;exact hgi.integrableOn
  · intro A hA _
    have hAg : MeasurableSet A:=hm A hA
    have he:=hpair (A.indicator (fun _=>1)) (measurable_const.indicator hA)
      (fun x=>by by_cases hx:x∈A <;> simp [hx])
    have hf' : (fun x=>A.indicator (fun _=>1) x*f x)=A.indicator f:=by
      funext x;by_cases hx:x∈A <;> simp [hx]
    have hg' : (fun x=>A.indicator (fun _=>1) x*g x)=A.indicator g:=by
      funext x;by_cases hx:x∈A <;> simp [hx]
    rw [hf',hg',integral_indicator hAg,integral_indicator hAg] at he
    exact he.symm
  · exact hg.aestronglyMeasurable

end FourPapersCommon
