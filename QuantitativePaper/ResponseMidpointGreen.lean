module
public import QuantitativePaper.ResponseTent

@[expose] public section

/-! Genuine scalar midpoint Green identity with continuous one-sided endpoint
values and actual derivatives in the open interval. -/
noncomputable section
open MeasureTheory Set
namespace QuantitativePaper
set_option maxHeartbeats 1800000

 theorem response_midpoint_green_identity (f f₁ f₂ : ℝ→ℝ)
    (hf : ContinuousOn f (Icc (0:ℝ) 1)) (hf₁ : ContinuousOn f₁ (Icc (0:ℝ) 1))
    (hdf : ∀x∈Ioo (0:ℝ) 1,HasDerivAt f (f₁ x) x)
    (hdf₁ : ∀x∈Ioo (0:ℝ) 1,HasDerivAt f₁ (f₂ x) x)
    (hi₂ : IntervalIntegrable f₂ volume 0 1) :
    f 0+f 1-2*f (1/2)=∫θ in (0:ℝ)..1,min θ (1-θ)*f₂ θ := by
  have hsub₀ : Icc (0:ℝ) (1/2)⊆Icc (0:ℝ) 1 := by intro x hx; exact ⟨hx.1,by linarith [hx.2]⟩
  have hsub₁ : Icc (1/2:ℝ) 1⊆Icc (0:ℝ) 1 := by intro x hx; exact ⟨by linarith [hx.1],hx.2⟩
  have hu₀ : uIcc (0:ℝ) (1/2)=Icc (0:ℝ) (1/2):=uIcc_of_le (by norm_num)
  have hu₁ : uIcc (1/2:ℝ) 1=Icc (1/2:ℝ) 1:=uIcc_of_le (by norm_num)
  have hu : uIcc (0:ℝ) 1=Icc (0:ℝ) 1:=uIcc_of_le (by norm_num)
  have hi₁ : IntervalIntegrable f₁ volume 0 1 :=
    (show ContinuousOn f₁ (uIcc (0:ℝ) 1) by simpa using hf₁).intervalIntegrable
  have hi₁L : IntervalIntegrable f₁ volume 0 (1/2) := hi₁.mono_set (by simpa only [hu₀,hu] using hsub₀)
  have hi₁R : IntervalIntegrable f₁ volume (1/2) 1 := hi₁.mono_set (by simpa only [hu₁,hu] using hsub₁)
  have hi₂L : IntervalIntegrable f₂ volume 0 (1/2) := hi₂.mono_set (by simpa only [hu₀,hu] using hsub₀)
  have hi₂R : IntervalIntegrable f₂ volume (1/2) 1 := hi₂.mono_set (by simpa only [hu₁,hu] using hsub₁)
  have hlFTC:=intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ)≤1/2)
    (hf.mono hsub₀) (fun x hx=>hdf x ⟨hx.1,by linarith [hx.2]⟩) hi₁L
  have hrFTC:=intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (1/2:ℝ)≤1)
    (hf.mono hsub₁) (fun x hx=>hdf x ⟨by linarith [hx.1],hx.2⟩) hi₁R
  have hleft:=intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u:=fun x : ℝ=>x) (v:=f₁) (u':=fun _=>(1:ℝ)) (v':=f₂)
    continuous_id.continuousOn (by simpa only [hu₀] using hf₁.mono hsub₀)
    (fun x _=>hasDerivAt_id x)
    (fun x hx=>by
      have hh : x∈Ioo (0:ℝ) (1/2):=by simpa only [min_eq_left (by norm_num : (0:ℝ)≤1/2),max_eq_right (by norm_num : (0:ℝ)≤1/2)] using hx
      exact hdf₁ x ⟨hh.1,by linarith [hh.2]⟩)
    intervalIntegrable_const hi₂L
  have hright:=intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u:=fun x : ℝ=>1-x) (v:=f₁) (u':=fun _=>(-1:ℝ)) (v':=f₂)
    (continuous_const.sub continuous_id).continuousOn (by simpa only [hu₁] using hf₁.mono hsub₁)
    (fun x _=>by simpa using (hasDerivAt_id x).const_sub (1:ℝ))
    (fun x hx=>by
      have hh : x∈Ioo (1/2:ℝ) 1:=by simpa only [min_eq_left (by norm_num : (1/2:ℝ)≤1),max_eq_right (by norm_num : (1/2:ℝ)≤1)] using hx
      exact hdf₁ x ⟨by linarith [hh.1],hh.2⟩)
    intervalIntegrable_const hi₂R
  have hp : IntervalIntegrable (fun θ=>min θ (1-θ)*f₂ θ) volume 0 1 :=
    hi₂.continuousOn_mul ((continuous_id.min (continuous_const.sub continuous_id)).continuousOn)
  have hpL : IntervalIntegrable (fun θ=>min θ (1-θ)*f₂ θ) volume 0 (1/2):=hp.mono_set (by simpa only [hu₀,hu] using hsub₀)
  have hpR : IntervalIntegrable (fun θ=>min θ (1-θ)*f₂ θ) volume (1/2) 1:=hp.mono_set (by simpa only [hu₁,hu] using hsub₁)
  rw [←intervalIntegral.integral_add_adjacent_intervals hpL hpR]
  have heL : (∫θ in (0:ℝ)..1/2,min θ (1-θ)*f₂ θ)=∫θ in (0:ℝ)..1/2,θ*f₂ θ := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    change min θ (1-θ)*f₂ θ=θ*f₂ θ
    rw [hu₀] at hθ
    rw [min_eq_left (by linarith [hθ.2] : θ≤1-θ)]
  have heR : (∫θ in (1/2:ℝ)..1,min θ (1-θ)*f₂ θ)=∫θ in (1/2:ℝ)..1,(1-θ)*f₂ θ := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    change min θ (1-θ)*f₂ θ=(1-θ)*f₂ θ
    rw [hu₁] at hθ
    rw [min_eq_right (by linarith [hθ.1] : 1-θ≤θ)]
  rw [heL,heR]
  simp only [one_mul,neg_one_mul,zero_mul,sub_self,mul_zero,
    intervalIntegral.integral_neg] at hleft hright
  rw [hleft,hright,hlFTC,hrFTC]
  ring

end QuantitativePaper
