module
public import QuantitativePaper.UniformScalarTrialExpectation
public import QuantitativeFollowup.ScalarBackwardEnergy

@[expose] public section

/-! Genuine backward energy control with a uniform rescaled drift/Hessian
bound. The exact contact moment retains the third localization power. -/
noncomputable section
open Set MeasureTheory Filter Paper FRSB FourPapersCommon QuantitativeFollowup
open scoped Topology NNReal
namespace QuantitativePaper
set_option maxHeartbeats 1600000

theorem scalarClipped_square_backward_uniform_bound (s : ℝ) (hs : s∈Icc (0:ℝ) 1)
    (β : ℝ) (hβ : 0<β) (μ : Paper.ParisiMeasure) (hmin : IsParisiMinimizer β 0 μ)
    (q : ℝ) (hq : q∈Ioo (0:ℝ) 1) (hsupp : parisiSupport μ=Icc (0:ℝ) q)
    (lam C L T : ℝ) (hlam : β*s=lam) (hlamL : lam≤L) (hC : 0≤C) (hL : 0≤L)
    (hT : 0<T) (hTq : T<q) (hfloor : s≤parisiCDF μ T)
    (hcoeff : ∀t∈Icc (0:ℝ) T,β*parisiCDF μ t≤L)
    (hH : ∀t∈Icc (0:ℝ) T,∀x,β*parisiHessian β μ (t,x)≤C) :
    ∀r∈Icc (0:ℝ) T,
      scalarSquareDifferenceMomentReal β hβ.ne' μ (scalarClippedTrialMeasure s hs μ) r≤
        lam^2*C^2*T^3*Real.exp ((9*L^2+2*L*C+1/T)*(T-r)) := by
  let ν:=scalarClippedTrialMeasure s hs μ
  let Y:=scalarSquareDifferenceMomentReal β hβ.ne' μ ν
  let source : ℝ→Paper.BrownianSample→ℝ:=fun t ω=>
    scalarClippingSquareSource β μ ν (t,selectedParisiItoState β 0 hβ.ne' μ t.toNNReal ω)
  let m : ℝ→ℝ:=fun t=>∫ω,source t ω∂canonicalBrownianMeasure
  have hsm : Measurable (Function.uncurry source):=
    (measurable_scalarClippingSquareSource β μ ν).comp
      (measurable_fst.prodMk (measurable_selectedState_real β hβ.ne' μ))
  have hmI (a b : ℝ) : IntervalIntegrable m volume a b :=
    intervalIntegrable_bounded_source_expectation source hsm (40*β^2)
      (fun t ω=>norm_scalarClippingSquareSource_le β μ ν _) a b
  have hYc : Continuous Y:=continuous_scalarSquareDifferenceMomentReal β hβ.ne' μ ν
  have hY0 : ∀r∈Icc (0:ℝ) T,0≤Y r:=fun r _=>scalarSquareDifferenceMoment_nonneg β hβ.ne' μ ν r.toNNReal
  have hYZ : Y T=0:=scalarClipped_square_terminal_zero s hs β hβ.ne' μ T.toNNReal
    (by simpa only [Real.coe_toNNReal T hT.le] using hTq.le.trans hq.2.le)
    (by simpa only [Real.coe_toNNReal T hT.le] using hfloor)
  have hineq : ∀r∈Icc (0:ℝ) T,Y r≤lam^2*C^2*T^3+
      ((9*L^2+2*L*C+1/T))*(∫t in 0..(T-r),Y (T-t)) := by
    intro r hr
    have hid:=scalarClipped_square_interval s hs β hβ.ne' μ hmin q hq hsupp r.toNNReal T.toNNReal
      (Real.toNNReal_mono hr.2) (by simpa only [Real.coe_toNNReal T hT.le] using hTq)
    change Y T-Y r=∫t in (r.toNNReal:ℝ)..(T.toNNReal:ℝ),m t at hid
    rw [Real.coe_toNNReal r hr.1,Real.coe_toNNReal T hT.le,hYZ] at hid
    have hyEq : Y r=∫t in r..T,-m t := by
      rw [intervalIntegral.integral_neg]
      linarith [hid]
    have hmono:=intervalIntegral.integral_mono_on hr.2 (hmI r T).neg
      (((hYc.intervalIntegrable r T).const_mul (9*L^2+2*L*C+1/T)).add
        ((continuous_id.intervalIntegrable r T).const_mul (lam^2*C^2*T)))
      (fun t ht=>scalarClipped_square_source_expectation_uniform_le s hs β hβ μ hmin q hq hsupp
        lam C L T t hlam hlamL hT ⟨hr.1.trans ht.1,ht.2.trans hTq.le⟩
        (hcoeff t ⟨hr.1.trans ht.1,ht.2⟩) (hH t ⟨hr.1.trans ht.1,ht.2⟩))
    change (∫t in r..T,-m t)≤∫t in r..T,(9*L^2+2*L*C+1/T)*Y t+lam^2*C^2*T*t at hmono
    have hidi : IntervalIntegrable (fun t : ℝ=>t) volume r T:=continuous_id.intervalIntegrable r T
    rw [←hyEq,intervalIntegral.integral_add ((hYc.intervalIntegrable r T).const_mul _) (hidi.const_mul _),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hmono
    have hiT : (∫t in r..T,t)≤T^2 := by
      have hh:=intervalIntegral.integral_mono_on hr.2 hidi
        (intervalIntegrable_const (μ:=volume) (c:=T)) (fun t ht=>ht.2)
      simp only [intervalIntegral.integral_const,smul_eq_mul] at hh
      have hrt:=mul_le_mul_of_nonneg_right (sub_le_self T hr.1) hT.le
      nlinarith
    have hmT:=mul_le_mul_of_nonneg_left hiT
      (show 0≤lam^2*C^2*T by positivity)
    have hiRev : (∫t in 0..(T-r),Y (T-t))=(∫t in r..T,Y t) := by
      rw [intervalIntegral.integral_comp_sub_left]
      congr 1 <;> ring
    rw [hiRev]
    nlinarith only [hmono,hmT]
  apply le_exp_of_reverse_integral_le Y hYc T (lam^2*C^2*T^3) ((9*L^2+2*L*C+1/T))
    (by positivity) (by positivity) hY0
  intro r hr
  simpa only [intervalIntegral.integral_comp_sub_left,sub_sub_cancel,sub_zero] using hineq r hr

theorem scalarClipped_square_uniform_energy_bound (s : ℝ) (hs : s∈Icc (0:ℝ) 1)
    (β : ℝ) (hβ : 0<β) (μ : Paper.ParisiMeasure) (hmin : IsParisiMinimizer β 0 μ)
    (q : ℝ) (hq : q∈Ioo (0:ℝ) 1) (hsupp : parisiSupport μ=Icc (0:ℝ) q)
    (lam C L T : ℝ) (hlam : β*s=lam) (hlamL : lam≤L) (hC : 0≤C) (hL : 0≤L)
    (hT : 0<T) (hTq : T<q) (hfloor : s≤parisiCDF μ T)
    (hcoeff : ∀t∈Icc (0:ℝ) T,β*parisiCDF μ t≤L)
    (hH : ∀t∈Icc (0:ℝ) T,∀x,β*parisiHessian β μ (t,x)≤C) :
    ∀r∈Icc (0:ℝ) T,
      scalarSquareDifferenceMomentReal β hβ.ne' μ (scalarClippedTrialMeasure s hs μ) r≤
        lam^2*C^2*Real.exp (9*L^2+2*L*C+1)*T^3 := by
  intro r hr
  apply (scalarClipped_square_backward_uniform_bound s hs β hβ μ hmin q hq hsupp lam C L T hlam hlamL hC hL hT hTq hfloor hcoeff hH r hr).trans
  have hh : (9*L^2+2*L*C+1/T)*(T-r)≤9*L^2+2*L*C+1 := by
    have hTr : T-r≤T:=sub_le_self _ hr.1
    have hc : 0≤9*L^2+2*L*C+1/T:=by positivity
    have ht1 : T≤1:=hTq.le.trans hq.2.le
    have hmul:=mul_le_mul_of_nonneg_left hTr hc
    have he : (9*L^2+2*L*C+1/T)*T=(9*L^2+2*L*C)*T+1 := by field_simp <;> ring
    rw [he] at hmul
    nlinarith [mul_le_mul_of_nonneg_left ht1 (show 0≤9*L^2+2*L*C by positivity)]
  have he:=Real.exp_le_exp.mpr hh
  convert! mul_le_mul_of_nonneg_left he (show 0≤lam^2*C^2*T^3 by positivity) using 1 <;> ring


end QuantitativePaper
