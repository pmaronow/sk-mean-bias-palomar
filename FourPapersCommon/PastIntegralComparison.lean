module
public import FourPapersCommon.PullbackIndicatorIntegral
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral

@[expose] public section

/-! Order is determined by bounded nonnegative tests measurable in a
sub-sigma-algebra, when both compared functions are adapted to it. -/
noncomputable section
open Set MeasureTheory
namespace FourPapersCommon
variable {Ω : Type*}

theorem ae_le_of_past_setIntegral_le (m : MeasurableSpace Ω) [m0 : MeasurableSpace Ω]
    (P : Measure Ω) (hm : m≤m0) (f g : Ω→ℝ)
    (hfm : StronglyMeasurable[m] f) (hgm : StronglyMeasurable[m] g)
    (hf : Integrable f P) (hg : Integrable g P)
    (hfg : ∀A,MeasurableSet[m] A→(∫x in A,f x ∂P)≤∫x in A,g x ∂P) :
    f≤ᵐ[P]g := by
  apply ae_of_ae_trim hm
  apply ae_le_of_forall_setIntegral_le (hf.trim hm hfm) (hg.trim hm hgm)
  intro A hA _
  rw [←setIntegral_trim hm hfm hA,←setIntegral_trim hm hgm hA]
  exact hfg A hA

theorem ae_le_of_past_bounded_nonneg_tests (m : MeasurableSpace Ω) [m0 : MeasurableSpace Ω]
    (P : Measure Ω) (hm : m≤m0) (f g : Ω→ℝ)
    (hfm : StronglyMeasurable[m] f) (hgm : StronglyMeasurable[m] g)
    (hf : Integrable f P) (hg : Integrable g P)
    (hfg : ∀Z : Ω→ℝ,Measurable[m] Z→(∀x,0≤Z x)→(∀x,‖Z x‖≤1)→
      (∫x,Z x*f x ∂P)≤∫x,Z x*g x ∂P) : f≤ᵐ[P]g := by
  apply ae_le_of_past_setIntegral_le m P hm f g hfm hgm hf hg
  intro A hA
  have he:=hfg (A.indicator (fun _=>1)) (measurable_const.indicator hA)
    (fun x=>by by_cases hx:x∈A <;> simp [hx])
    (fun x=>by by_cases hx:x∈A <;> simp [hx])
  have hind (F : Ω→ℝ) : (∫x,A.indicator (fun _=>1) x*F x ∂P)=∫x in A,F x ∂P := by
    rw [←integral_indicator (hm A hA)]
    apply integral_congr_ae
    exact .of_forall fun x=>by by_cases hx:x∈A <;> simp [hx]
  rw [hind,hind] at he
  exact he

end FourPapersCommon
