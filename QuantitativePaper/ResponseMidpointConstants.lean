module
public import QuantitativePaper.ResponseMidpointGreen
public import QuantitativePaper.ResponseTentDerivative

@[expose] public section

/-! Exact scalar tent-to-midpoint constants. These supporting inequalities
retain explicit curvature inputs; the actual response/Dynkin instantiation
is supplied separately. -/
noncomputable section
open MeasureTheory Set
namespace QuantitativePaper
set_option maxHeartbeats 1800000

 theorem response_tent_curvature_constant (c r κ ell b sigma P X R : ℝ)
    (hr : 0≤r) (hκ : 0≤κ) (hell : 0<ell) (hb : 0<b) (hsigma : 0≤sigma)
    (hXpos : 0<X) (hP : c^2*κ*ell/4≤P) (hX : X≤8*b/ell+2*sigma)
    (hR : r^3*P^2/X≤R) :
    c^4*r^3*κ^2*ell^3/(32*(8*b+ell*sigma))≤R := by
  let L:=c^2*κ*ell/4
  let D:=8*b+ell*sigma
  have hD : 0<D:=add_pos_of_pos_of_nonneg (mul_pos (by norm_num) hb) (mul_nonneg hell.le hsigma)
  have hL : 0≤L:=div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg c) hκ) hell.le) (by norm_num)
  have hPsq : L^2≤P^2:=(sq_le_sq₀ hL (hL.trans hP)).mpr hP
  have hx : ell*X≤2*D := by
    have h:=mul_le_mul_of_nonneg_left hX hell.le
    have he : ell*(8*b/ell+2*sigma)=8*b+2*ell*sigma:=by field_simp <;> ring
    rw [he] at h
    dsimp [D]
    nlinarith
  have hfrac : ell/(2*D)≤1/X := by
    apply (div_le_div_iff₀ (by positivity : 0<2*D) hXpos).mpr
    nlinarith
  have hnum : 0≤r^3*L^2:=mul_nonneg (pow_nonneg hr 3) (sq_nonneg _)
  calc
    c^4*r^3*κ^2*ell^3/(32*(8*b+ell*sigma))=r^3*L^2*(ell/(2*D)) := by
      dsimp [L,D]
      field_simp
      ring
    _≤r^3*L^2*(1/X):=mul_le_mul_of_nonneg_left hfrac hnum
    _≤r^3*P^2/X := by
      simpa only [div_eq_mul_inv,one_mul] using div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hPsq (pow_nonneg hr 3)) hXpos.le
    _≤R:=hR

 theorem response_midpoint_weight_integral :
    (∫θ in (0:ℝ)..1,min θ (1-θ))=1/4 := by
  have hc : Continuous (fun θ : ℝ=>min θ (1-θ)):=continuous_id.min (continuous_const.sub continuous_id)
  rw [←intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 (1/2))
    (hc.intervalIntegrable (1/2) 1)]
  have hl : (∫θ in (0:ℝ)..1/2,min θ (1-θ))=∫θ in (0:ℝ)..1/2,θ := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    change min θ (1-θ)=θ
    have hh : θ≤1/2 := by rw [uIcc_of_le (by norm_num : (0:ℝ)≤1/2)] at hθ;exact hθ.2
    exact min_eq_left (by linarith)
  have hr : (∫θ in (1/2:ℝ)..1,min θ (1-θ))=∫θ in (1/2:ℝ)..1,1-θ := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    change min θ (1-θ)=1-θ
    have hh : 1/2≤θ := by rw [uIcc_of_le (by norm_num : (1/2:ℝ)≤1)] at hθ;exact hθ.1
    exact min_eq_right (by linarith)
  have hlin : (∫θ in (1/2:ℝ)..1,1-θ)=(∫θ in (1/2:ℝ)..1,(1:ℝ))-(∫θ in (1/2:ℝ)..1,θ) := by
    simpa only [id_eq] using intervalIntegral.integral_sub (f:=fun _ : ℝ=>(1:ℝ)) (g:=id)
      intervalIntegrable_const (continuous_id.intervalIntegrable (1/2) 1)
  rw [hl,hr,hlin,integral_id,integral_id,intervalIntegral.integral_const]
  norm_num

 theorem response_midpoint_lower_of_second_derivative (f f₁ f₂ : ℝ→ℝ)
    (hf : ContinuousOn f (Icc (0:ℝ) 1)) (hf₁ : ContinuousOn f₁ (Icc (0:ℝ) 1))
    (hdf : ∀x∈Ioo (0:ℝ) 1,HasDerivAt f (f₁ x) x)
    (hdf₁ : ∀x∈Ioo (0:ℝ) 1,HasDerivAt f₁ (f₂ x) x)
    (hi₂ : IntervalIntegrable f₂ volume 0 1) (C : ℝ)
    (hlo : ∀θ∈Ioo (0:ℝ) 1,C≤f₂ θ) :
    C/4≤f 0+f 1-2*f (1/2) := by
  let W:=fun θ : ℝ=>min θ (1-θ)
  have hW : Continuous W:=continuous_id.min (continuous_const.sub continuous_id)
  have hiR : IntegrableOn (fun θ=>W θ*f₂ θ) (Ioc (0:ℝ) 1) := by
    have hi:=hi₂.continuousOn_mul hW.continuousOn
    exact hi.1
  have hiL : IntegrableOn (fun θ=>C*W θ) (Ioc (0:ℝ) 1) :=
    (continuous_const.mul hW).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hineq : (fun θ=>C*W θ)≤ᵐ[volume.restrict (Ioc (0:ℝ) 1)] (fun θ=>W θ*f₂ θ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne (1:ℝ))] with θ hθ hne
    have hθ' : θ∈Ioo (0:ℝ) 1:=⟨hθ.1,lt_of_le_of_ne hθ.2 hne⟩
    have hw : 0≤W θ:=le_min hθ'.1.le (sub_nonneg.mpr hθ'.2.le)
    simpa only [mul_comm C] using mul_le_mul_of_nonneg_left (hlo θ hθ') hw
  have hi:=integral_mono_ae hiL hiR hineq
  rw [←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    ←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),intervalIntegral.integral_const_mul] at hi
  change C*(∫θ in (0:ℝ)..1,min θ (1-θ))≤∫θ in (0:ℝ)..1,min θ (1-θ)*f₂ θ at hi
  rw [response_midpoint_weight_integral,←response_midpoint_green_identity f f₁ f₂ hf hf₁ hdf hdf₁ hi₂] at hi
  simpa only [div_eq_mul_inv,one_mul] using hi

 theorem response_midpoint_printed_constant (c r κ ell b sigma Gap : ℝ)
    (hGap : (c^4*r^3*κ^2*ell^3/(32*(8*b+ell*sigma)))/4≤Gap) :
    c^4*r^3*κ^2*ell^3/(128*(8*b+ell*sigma))≤Gap := by
  convert hGap using 1
  simp only [div_eq_mul_inv,mul_inv_rev]
  norm_num
  ring

end QuantitativePaper
