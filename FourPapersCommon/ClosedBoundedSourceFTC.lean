module
public import FourPapersCommon.ClosedNonnegativeSourceFTC

@[expose] public section

/-! A genuinely bounded signed local source closes its primitive identity
at continuous endpoints. This derives integrability from cropped identities;
no measurability, integrability, or endpoint identity is supplied. -/
noncomputable section
open Set MeasureTheory Filter
namespace FourPapersCommon
set_option maxHeartbeats 1000000

theorem closed_bounded_source_ftc (F g : ℝ→ℝ) (a b M : ℝ)
    (hab : a≤b) (hF : ContinuousOn F (Icc a b))
    (hg : ∀x∈Ioo a b,|g x|≤M)
    (hlocal : ∀l∈Ioo a b,∀u∈Ioo a b,l≤u→
      IntegrableOn g (Ioc l u) volume ∧ F u-F l=∫x in l..u,g x) :
    IntegrableOn g (Ioc a b) volume ∧ F b-F a=∫x in a..b,g x := by
  have hFplus : ContinuousOn (fun x=>F x+M*x) (Icc a b):=
    hF.add (continuous_const.mul continuous_id).continuousOn
  have hlocalplus : ∀l∈Ioo a b,∀u∈Ioo a b,l≤u→
      IntegrableOn (fun x=>g x+M) (Ioc l u) volume ∧
      (F u+M*u)-(F l+M*l)=∫x in l..u,(g x+M) := by
    intro l hl u hu hlu
    obtain ⟨hi,he⟩:=hlocal l hl u hu hlu
    have hic : IntegrableOn (fun _ : ℝ=>M) (Ioc l u) volume:=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hlu).mp intervalIntegrable_const
    have hiint : IntervalIntegrable g volume l u:=intervalIntegrable_iff_integrableOn_Ioc_of_le hlu |>.mpr hi
    refine ⟨hi.add hic,?_⟩
    rw [intervalIntegral.integral_add hiint intervalIntegrable_const,
      intervalIntegral.integral_const,smul_eq_mul,←he]
    ring
  obtain ⟨hi,he⟩:=closed_nonnegative_source_ftc (fun x=>F x+M*x) (fun x=>g x+M)
    a b hab hFplus (fun x hx=>by linarith [(abs_le.mp (hg x hx)).1]) hlocalplus
  have hic : IntegrableOn (fun _ : ℝ=>M) (Ioc a b) volume:=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp intervalIntegrable_const
  have hig : IntegrableOn g (Ioc a b) volume:=by
    have hsub : (fun x=>g x+M)-(fun _ : ℝ=>M)=g:=by
      funext x
      simp only [Pi.sub_apply,add_sub_cancel_right]
    simpa only [hsub] using hi.sub hic
  have hiint : IntervalIntegrable g volume a b:=intervalIntegrable_iff_integrableOn_Ioc_of_le hab |>.mpr hig
  rw [intervalIntegral.integral_add hiint intervalIntegrable_const,
    intervalIntegral.integral_const,smul_eq_mul] at he
  exact ⟨hig,by linarith [he]⟩

end FourPapersCommon
