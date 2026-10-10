module
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section

/-! A moving last-field parameter needs no derivative of its zero-row
baseline. Genuine row-heat increments and continuous baseline coefficients
suffice because the baseline covariance vanishes identically. -/
noncomputable section
open Set Filter
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1400000

theorem cavity_zero_mul_continuousWithinAt {S : Set ℝ} (f g : ℝ→ℝ) (D : ℝ)
    (hf : HasDerivWithinAt f D S 0) (hf0 : f 0=0)
    (hg : ContinuousWithinAt g S 0) :
    HasDerivWithinAt (fun u=>f u*g u) (D*g 0) S 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have ht:=(hasDerivWithinAt_iff_tendsto_slope.mp hf).mul
    (hg.tendsto.mono_left (nhdsWithin_mono 0 sdiff_subset))
  apply ht.congr'
  exact .of_forall fun u=>by simp only [slope_def_field,hf0,zero_mul,sub_zero];ring

theorem cavity_moving_covariance_from_heat_increments
    (Z F G H Z0 F0 G0 H0 : ℝ→ℝ) (dZ dF dG dH : ℝ)
    (hZ : ContinuousWithinAt Z (Ici 0) 0)
    (hF0 : ContinuousWithinAt F0 (Ici 0) 0)
    (hG : ContinuousWithinAt G (Ici 0) 0)
    (hH0 : ContinuousWithinAt H0 (Ici 0) 0)
    (hz : Z 0=Z0 0) (hf : F 0=F0 0) (hg : G 0=G0 0) (hh : H 0=H0 0)
    (hp : Z 0≠0)
    (hbase : ∀ᶠ u in 𝓝[Ici (0:ℝ)] 0,H0 u*Z0 u=F0 u*G0 u)
    (hbase0 : H0 0*Z0 0=F0 0*G0 0)
    (hincZ : HasDerivWithinAt (fun u=>Z u-Z0 u) dZ (Ici 0) 0)
    (hincF : HasDerivWithinAt (fun u=>F u-F0 u) dF (Ici 0) 0)
    (hincG : HasDerivWithinAt (fun u=>G u-G0 u) dG (Ici 0) 0)
    (hincH : HasDerivWithinAt (fun u=>H u-H0 u) dH (Ici 0) 0) :
    HasDerivWithinAt (fun u=>H u/Z u-(F u/Z u)*(G u/Z u))
      ((dH*Z 0+H0 0*dZ-dF*G 0-F0 0*dG)/(Z 0)^2) (Ici 0) 0 := by
  let N:=fun u=>(H u-H0 u)*Z u+H0 u*(Z u-Z0 u)-
    (F u-F0 u)*G u-F0 u*(G u-G0 u)
  have hiH:=cavity_zero_mul_continuousWithinAt _ Z dH hincH (by rw [hh];ring) hZ
  have hiZ : HasDerivWithinAt (fun u=>H0 u*(Z u-Z0 u)) (dZ*H0 0) (Ici (0:ℝ)) 0 :=
    (cavity_zero_mul_continuousWithinAt _ H0 dZ hincZ (by rw [hz];ring) hH0).congr_of_mem
      (fun u _=>by ring) (by simp)
  have hiF:=cavity_zero_mul_continuousWithinAt _ G dF hincF (by rw [hf];ring) hG
  have hiG : HasDerivWithinAt (fun u=>F0 u*(G u-G0 u)) (dG*F0 0) (Ici (0:ℝ)) 0 :=
    (cavity_zero_mul_continuousWithinAt _ F0 dG hincG (by rw [hg];ring) hF0).congr_of_mem
      (fun u _=>by ring) (by simp)
  have hN : HasDerivWithinAt N
      (dH*Z 0+H0 0*dZ-dF*G 0-F0 0*dG) (Ici 0) 0 := by
    convert (hiH.add hiZ).sub hiF |>.sub hiG using 1 <;> ring
  have hN0:N 0=0:=by dsimp only [N];rw [hz,hf,hg,hh];ring
  have hi : ContinuousWithinAt (fun u=>(Z u)^2) (Ici 0) 0:=hZ.pow 2
  have hv : ContinuousWithinAt (fun u=>((Z u)^2)⁻¹) (Ici 0) 0:=hi.inv₀ (pow_ne_zero _ hp)
  have hd:=(cavity_zero_mul_continuousWithinAt N _ _ hN hN0 hv)
  have he : (fun u=>N u*((Z u)^2)⁻¹)=ᶠ[𝓝[Ici (0:ℝ)] 0]
      (fun u=>H u/Z u-(F u/Z u)*(G u/Z u)) := by
    filter_upwards [hbase] with u hu
    dsimp only [N]
    rw [show (H u-H0 u)*Z u+H0 u*(Z u-Z0 u)-
      (F u-F0 u)*G u-F0 u*(G u-G0 u)=H u*Z u-F u*G u by nlinarith [hu]]
    by_cases hzu:Z u=0
    · simp [hzu]
    · field_simp
      <;> ring
  have he0:N 0*((Z 0)^2)⁻¹=H 0/Z 0-(F 0/Z 0)*(G 0/Z 0) := by
    rw [hN0,zero_mul]
    field_simp [hp]
    rw [hz,hf,hg,hh]
    nlinarith [hbase0]
  simpa only [div_eq_mul_inv] using hd.congr_of_eventuallyEq he.symm he0.symm

end QuantitativeFollowup
