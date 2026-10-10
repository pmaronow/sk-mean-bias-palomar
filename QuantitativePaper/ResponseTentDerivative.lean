module
public import QuantitativePaper.ResponseTent

@[expose] public section

/-! Actual tent derivatives and their exact squared integral, with the three
corner points removed only on the genuine Lebesgue null set. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace QuantitativePaper
set_option maxHeartbeats 1800000

 theorem hasDerivAt_responseTent_left_zero {ell q : ℝ} (hell : 0<ell) (hq : q<ell/4) :
    HasDerivAt (responseTent ell) 0 q := by
  apply (hasDerivAt_const q (0:ℝ)).congr_of_eventuallyEq
  exact (eventually_lt_nhds hq).mono fun x hx=>responseTent_zero_left hell hx.le

 theorem hasDerivAt_responseTent_right_zero {ell q : ℝ} (hell : 0<ell) (hq : 3*ell/4<q) :
    HasDerivAt (responseTent ell) 0 q := by
  apply (hasDerivAt_const q (0:ℝ)).congr_of_eventuallyEq
  exact (eventually_gt_nhds hq).mono fun x hx=>responseTent_zero_right hell hx.le

 theorem hasDerivAt_responseTent_left {ell q : ℝ} (hell : 0<ell)
    (hq : q∈Ioo (ell/4) (ell/2)) : HasDerivAt (responseTent ell) (4/ell) q := by
  have h:=(((hasDerivAt_id q).const_mul 4).div_const ell).sub_const 1
  simp only [mul_one] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hq.1,eventually_lt_nhds hq.2] with x hx₁ hx₂
  exact responseTent_left_formula hell ⟨hx₁.le,hx₂.le⟩

 theorem hasDerivAt_responseTent_right {ell q : ℝ} (hell : 0<ell)
    (hq : q∈Ioo (ell/2) (3*ell/4)) : HasDerivAt (responseTent ell) (-(4/ell)) q := by
  have h:=(hasDerivAt_const q (3:ℝ)).sub (((hasDerivAt_id q).const_mul 4).div_const ell)
  simp only [mul_one,zero_sub] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hq.1,eventually_lt_nhds hq.2] with x hx₁ hx₂
  exact responseTent_right_formula hell ⟨hx₁.le,hx₂.le⟩

 theorem ae_deriv_responseTent {ell : ℝ} (hell : 0<ell) :
    deriv (responseTent ell)=ᵐ[volume] responseTentSlope ell := by
  filter_upwards [volume.ae_ne (ell/4),volume.ae_ne (ell/2),volume.ae_ne (3*ell/4)]
    with q hq₁ hq₂ hq₃
  by_cases h₁ : q<ell/4
  · simpa only [responseTentSlope,if_pos h₁] using (hasDerivAt_responseTent_left_zero hell h₁).deriv
  · by_cases h₂ : q<ell/2
    · have hx : ell/4<q:=lt_of_le_of_ne (le_of_not_gt h₁) (Ne.symm hq₁)
      simpa only [responseTentSlope,if_neg h₁,if_pos h₂] using (hasDerivAt_responseTent_left hell ⟨hx,h₂⟩).deriv
    · by_cases h₃ : q<3*ell/4
      · have hx : ell/2<q:=lt_of_le_of_ne (le_of_not_gt h₂) (Ne.symm hq₂)
        simpa only [responseTentSlope,if_neg h₁,if_neg h₂,if_pos h₃] using
          (hasDerivAt_responseTent_right hell ⟨hx,h₃⟩).deriv
      · have hx : 3*ell/4<q:=lt_of_le_of_ne (le_of_not_gt h₃) (Ne.symm hq₃)
        simpa only [responseTentSlope,if_neg h₁,if_neg h₂,if_neg h₃] using
          (hasDerivAt_responseTent_right_zero hell hx).deriv

 theorem responseTentSlope_sq {ell : ℝ} (hell : 0<ell) :
    (fun q=>(responseTentSlope ell q)^2)=
      (Ico (ell/4) (3*ell/4)).indicator (fun _=>(4/ell)^2) := by
  funext q
  by_cases h₁ : q<ell/4
  · have hn : q∉Ico (ell/4) (3*ell/4):=fun h=>not_lt_of_ge h.1 h₁
    simp [responseTentSlope,h₁,hn]
  · by_cases h₃ : q<3*ell/4
    · have hm : q∈Ico (ell/4) (3*ell/4):=⟨le_of_not_gt h₁,h₃⟩
      by_cases h₂ : q<ell/2 <;> simp [responseTentSlope,h₁,h₂,h₃,hm,neg_sq]
    · have hn : q∉Ico (ell/4) (3*ell/4):=fun h=>h₃ h.2
      have h₂ : ¬q<ell/2:=by intro h;apply h₃;linarith
      simp [responseTentSlope,h₁,h₂,h₃,hn]

 theorem responseTent_deriv_sq_integral {ell : ℝ} (hell : 0<ell) :
    (∫q,|deriv (responseTent ell) q|^2)=8/ell := by
  have he : (fun q=>|deriv (responseTent ell) q|^2)=ᵐ[volume]
      (fun q=>(responseTentSlope ell q)^2) :=
    (ae_deriv_responseTent hell).mono fun q hq=>by dsimp only; rw [hq,sq_abs]
  rw [integral_congr_ae he,responseTentSlope_sq hell,
    integral_indicator_const _ measurableSet_Ico,Real.volume_real_Ico,
    max_eq_left (by linarith : 0≤3*ell/4-ell/4)]
  simp only [smul_eq_mul]
  field_simp
  ring

 theorem integrable_responseTent_deriv_sq {ell : ℝ} (hell : 0<ell) :
    Integrable (fun q=>|deriv (responseTent ell) q|^2) := by
  have he : (fun q=>|deriv (responseTent ell) q|^2)=ᵐ[volume]
      (Ico (ell/4) (3*ell/4)).indicator (fun _=>(4/ell)^2) := by
    filter_upwards [ae_deriv_responseTent hell] with q hq
    rw [hq,sq_abs]
    exact congrFun (responseTentSlope_sq hell) q
  apply Integrable.congr ?_ he.symm
  have hi : IntegrableOn (fun _ : ℝ=>(4/ell)^2) (Ico (ell/4) (3*ell/4)) := integrable_const _
  exact hi.integrable_indicator measurableSet_Ico

end QuantitativePaper
