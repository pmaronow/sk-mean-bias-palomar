module
public import QuantitativePaper.ResponseMidpointGreen
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

/-! Cropped midpoint curvature estimates use only genuine interior
derivatives. Endpoint derivative extensions are not assumed. -/
noncomputable section
open MeasureTheory Set
namespace QuantitativePaper
set_option maxHeartbeats 1600000

theorem response_cropped_midpoint_green (f f₁ f₂ : ℝ→ℝ)
    (hf : ContinuousOn f (Icc (0:ℝ) 1))
    (hdf : ∀x∈Ioo (0:ℝ) 1,HasDerivAt f (f₁ x) x)
    (hdf₁ : ∀x∈Ioo (0:ℝ) 1,HasDerivAt f₁ (f₂ x) x)
    (a b : ℝ) (ha : 0<a) (ham : a<1/2) (hmb : 1/2<b) (hb : b<1)
    (hi₂ : IntervalIntegrable f₂ volume a b) :
    (∫θ in a..b,min θ (1-θ)*f₂ θ)=
      f a+f b-2*f (1/2)-a*f₁ a+(1-b)*f₁ b:=by
  have hab : a≤b:=by linarith
  have hab01 : Icc a b⊆Ioo (0:ℝ) 1:=by intro x hx;exact ⟨ha.trans_le hx.1,hx.2.trans_lt hb⟩
  have h1 : ContinuousOn f₁ (Icc a b):=by
    intro x hx
    exact (hdf₁ x (hab01 hx)).continuousAt.continuousWithinAt
  have hf1 : IntervalIntegrable f₁ volume a b:=by
    exact (show ContinuousOn f₁ (uIcc a b) by rwa [uIcc_of_le hab]).intervalIntegrable
  have hL : uIcc a (1/2)⊆uIcc a b:=by rw [uIcc_of_le ham.le,uIcc_of_le hab];exact Icc_subset_Icc_right hmb.le
  have hR : uIcc (1/2) b⊆uIcc a b:=by rw [uIcc_of_le hmb.le,uIcc_of_le hab];exact Icc_subset_Icc_left ham.le
  have hlFTC:=intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ham.le
    (hf.mono (by intro x hx;exact ⟨ha.le.trans hx.1,(hx.2.trans hmb.le).trans hb.le⟩))
    (fun x hx=>hdf x ⟨ha.trans hx.1,(hx.2.trans hmb).trans hb⟩) (hf1.mono_set hL)
  have hrFTC:=intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hmb.le
    (hf.mono (by intro x hx;exact ⟨ha.le.trans (ham.le.trans hx.1),hx.2.trans hb.le⟩))
    (fun x hx=>hdf x ⟨ha.trans (ham.trans hx.1),hx.2.trans hb⟩) (hf1.mono_set hR)
  have hleft:=intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u:=fun x : ℝ=>x) (v:=f₁) (u':=fun _=>(1:ℝ)) (v':=f₂)
    continuous_id.continuousOn (h1.mono (by simpa only [uIcc_of_le ham.le,uIcc_of_le hab] using hL))
    (fun x _=>hasDerivAt_id x)
    (fun x hx=>by
      rw [min_eq_left ham.le,max_eq_right ham.le] at hx
      exact hdf₁ x ⟨ha.trans hx.1,(hx.2.trans hmb).trans hb⟩)
    intervalIntegrable_const (hi₂.mono_set hL)
  have hright:=intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u:=fun x : ℝ=>1-x) (v:=f₁) (u':=fun _=>(-1:ℝ)) (v':=f₂)
    (continuous_const.sub continuous_id).continuousOn
    (h1.mono (by simpa only [uIcc_of_le hmb.le,uIcc_of_le hab] using hR))
    (fun x _=>by simpa using (hasDerivAt_id x).const_sub (1:ℝ))
    (fun x hx=>by
      rw [min_eq_left hmb.le,max_eq_right hmb.le] at hx
      exact hdf₁ x ⟨ha.trans (ham.trans hx.1),hx.2.trans hb⟩)
    intervalIntegrable_const (hi₂.mono_set hR)
  have hp : IntervalIntegrable (fun θ=>min θ (1-θ)*f₂ θ) volume a b:=
    hi₂.continuousOn_mul ((continuous_id.min (continuous_const.sub continuous_id)).continuousOn)
  rw [←intervalIntegral.integral_add_adjacent_intervals (hp.mono_set hL) (hp.mono_set hR)]
  have heL : (∫θ in a..(1/2),min θ (1-θ)*f₂ θ)=∫θ in a..(1/2),θ*f₂ θ:=by
    apply intervalIntegral.integral_congr
    intro θ hθ
    change min θ (1-θ)*f₂ θ=θ*f₂ θ
    rw [uIcc_of_le ham.le] at hθ
    rw [min_eq_left (by linarith [hθ.2] : θ≤1-θ)]
  have heR : (∫θ in (1/2)..b,min θ (1-θ)*f₂ θ)=∫θ in (1/2)..b,(1-θ)*f₂ θ:=by
    apply intervalIntegral.integral_congr
    intro θ hθ
    change min θ (1-θ)*f₂ θ=(1-θ)*f₂ θ
    rw [uIcc_of_le hmb.le] at hθ
    rw [min_eq_right (by linarith [hθ.1] : 1-θ≤θ)]
  rw [heL,heR]
  simp only [one_mul,neg_one_mul,intervalIntegral.integral_neg] at hleft hright
  rw [hleft,hright,hlFTC,hrFTC]
  ring

theorem response_cropped_curvature_le_midpoint (f f₁ f₂ : ℝ→ℝ)
    (hf : ContinuousOn f (Icc (0:ℝ) 1)) (hconv : ConvexOn ℝ (Icc (0:ℝ) 1) f)
    (hdf : ∀x∈Ioo (0:ℝ) 1,HasDerivAt f (f₁ x) x)
    (hdf₁ : ∀x∈Ioo (0:ℝ) 1,HasDerivAt f₁ (f₂ x) x)
    (a b : ℝ) (ha : 0<a) (ham : a<1/2) (hmb : 1/2<b) (hb : b<1)
    (hi₂ : IntervalIntegrable f₂ volume a b) :
    (∫θ in a..b,min θ (1-θ)*f₂ θ)≤f 0+f 1-2*f (1/2):=by
  rw [response_cropped_midpoint_green f f₁ f₂ hf hdf hdf₁ a b ha ham hmb hb hi₂]
  have hla:=hconv.slope_le_of_hasDerivAt (x:=0) (y:=a)
    (by constructor <;>norm_num) ⟨ha.le,by linarith⟩ ha (hdf a ⟨ha,by linarith⟩)
  have hlb:=hconv.le_slope_of_hasDerivAt (x:=b) (y:=1)
    ⟨by linarith,hb.le⟩ (by constructor <;>norm_num) hb (hdf b ⟨by linarith,hb⟩)
  rw [slope_def_field,sub_zero] at hla
  rw [slope_def_field] at hlb
  have hla':= (div_le_iff₀ ha).mp hla
  have hlb':= (le_div_iff₀ (by linarith : 0<1-b)).mp hlb
  nlinarith

end QuantitativePaper
