module
public import QuantitativeFollowup.IntegralFlowInitial

@[expose] public section

/-! A genuine initial-field derivative for measurable-time integral flows.
The linearized exponential is not assumed: its Volterra equation is
proved by the AC FTC, and the nonlinear difference has a quadratic error. -/
noncomputable section
open Set MeasureTheory Filter Paper FourPapersCommon
open scoped NNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 2600000

theorem integral_flow_quadratic_error (b H : ℝ → ℝ → ℝ) (L K A : ℝ≥0)
    (hb : Paper.IsBoundedMeasurableDrift b L K)
    (hHm : Measurable (Function.uncurry H)) (hH : ∀ s z,‖H s z‖ ≤ K)
    (hder : ∀ s z,HasDerivAt (b s) (H s z) z)
    (hHL : ∀ s,LipschitzWith A (H s))
    (T : ℝ) (hT : 0 ≤ T) (W : ℝ → ℝ) (X : ℝ → ℝ → ℝ)
    (hX : ∀ x,Continuous (X x))
    (hXe : ∀ x t,t∈Icc (0 : ℝ) T → X x t=x+W t+∫ s in 0..t,b s (X x s))
    (x y t : ℝ) (ht : t∈Icc (0 : ℝ) T) :
    ‖X y t-X x t-(y-x)*Real.exp (∫ s in 0..t,H s (X x s))‖ ≤
      A*T*Real.exp (3*K*T)*|y-x|^2 := by
  let c := fun s => H s (X x s)
  let Z := fun s => Real.exp (∫ u in 0..s,c u)
  let e := fun s => X y s-X x s-(y-x)*Z s
  have hcm : Measurable c := hHm.comp (measurable_id.prodMk (hX x).measurable)
  have hcb (s : ℝ) : ‖c s‖ ≤ K := hH s _
  have hci (a b : ℝ) : IntervalIntegrable c volume a b :=
    intervalIntegrable_const.mono_fun' hcm.aestronglyMeasurable (.of_forall hcb)
  have hZc : Continuous Z := Real.continuous_exp.comp
    (bounded_primitive_lipschitz c hcm K hcb).continuous
  have hZeq := exp_primitive_volterra c hcm K hcb T hT
  change ∀ s∈Icc (0 : ℝ) T,Z s=1+∫ u in 0..s,c u*Z u at hZeq
  have hec : Continuous e := ((hX y).sub (hX x)).sub (continuous_const.mul hZc)
  have hbi (z s : ℝ) : IntervalIntegrable (fun u => b u (X z u)) volume 0 s :=
    intervalIntegrable_const.mono_fun'
      (hb.measurable.comp (measurable_id.prodMk (hX z).measurable)).aestronglyMeasurable
      (.of_forall fun u => hb.norm_le u _)
  have hdiff := integral_state_initial_bound b L K hb T x y W (X x) (X y)
    (hX x) (hX y) (hXe x) (hXe y)
  have hdiffT (s : ℝ) (hs : s∈Icc (0 : ℝ) T) :
      ‖X y s-X x s‖ ≤ |y-x| * Real.exp (K*T) :=
    (hdiff s hs).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 K.coe_nonneg)) (abs_nonneg _))
  let R := A*|y-x|^2*Real.exp (2*K*T)
  have hR : 0 ≤ R := by dsimp only [R];positivity
  have hpoint (s : ℝ) (hs : s∈Icc (0 : ℝ) T) :
      ‖b s (X y s)-b s (X x s)-(y-x)*(c s*Z s)‖ ≤ K*‖e s‖+R := by
    have hrem := derivative_lipschitz_quadratic_remainder (b s) (H s) (hder s) A
      (hHL s) (X x s) (X y s)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) (hdiffT s hs) 2
    have hremR : ‖b s (X y s)-b s (X x s)-c s*(X y s-X x s)‖ ≤ R := by
      apply hrem.trans
      apply (mul_le_mul_of_nonneg_left hsq A.coe_nonneg).trans_eq
      dsimp only [R]
      have hexp : (Real.exp (K*T))^2=Real.exp (2*K*T) := by
        rw [←Real.exp_nat_mul]
        congr 1
        ring
      rw [mul_pow,hexp]
      ring
    rw [show b s (X y s)-b s (X x s)-(y-x)*(c s*Z s)=
      c s*e s+(b s (X y s)-b s (X x s)-c s*(X y s-X x s)) by dsimp only [e];ring]
    apply (norm_add_le _ _).trans
    rw [norm_mul]
    exact add_le_add (mul_le_mul_of_nonneg_right (hcb s) (norm_nonneg _)) hremR
  have heq (s : ℝ) (hs : s∈Icc (0 : ℝ) T) :
      e s=∫ u in 0..s,b u (X y u)-b u (X x u)-(y-x)*(c u*Z u) := by
    have hiZ : IntervalIntegrable (fun u => c u*Z u) volume 0 s :=
      (hci 0 s).mul_continuousOn hZc.continuousOn
    rw [intervalIntegral.integral_sub ((hbi y s).sub (hbi x s)) (hiZ.const_mul (y-x)),
      intervalIntegral.integral_sub (hbi y s) (hbi x s),intervalIntegral.integral_const_mul]
    change X y s-X x s-(y-x)*Z s=_
    rw [hXe y s hs,hXe x s hs,hZeq s hs]
    ring
  have hineq (s : ℝ) (hs : s∈Icc (0 : ℝ) T) :
      ‖e s‖ ≤ R*T+K*(∫ u in 0..s,‖e u‖) := by
    rw [heq s hs]
    have hib : IntervalIntegrable (fun u => b u (X y u)-b u (X x u)-(y-x)*(c u*Z u))
        volume 0 s := (hbi y s).sub (hbi x s) |>.sub
          (((hci 0 s).mul_continuousOn hZc.continuousOn).const_mul (y-x))
    have hm := intervalIntegral.integral_mono_on hs.1 hib.norm
      (((hec.norm.intervalIntegrable 0 s).const_mul (K : ℝ)).add intervalIntegrable_const)
      (fun u hu => hpoint u ⟨hu.1,hu.2.trans hs.2⟩)
    have hn := (intervalIntegral.norm_integral_le_integral_norm hs.1).trans hm
    rw [intervalIntegral.integral_add ((hec.norm.intervalIntegrable 0 s).const_mul (K : ℝ))
      intervalIntegrable_const,intervalIntegral.integral_const_mul,intervalIntegral.integral_const] at hn
    simp only [sub_zero,smul_eq_mul] at hn
    exact hn.trans (by nlinarith [mul_le_mul_of_nonneg_right hs.2 hR])
  have hg := le_exp_of_integral_le (fun s => ‖e s‖) hec.norm T (R*T) K
    (mul_nonneg hR hT) K.coe_nonneg (fun _ _ => norm_nonneg _) hineq
  have hout := (hg t ht).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 K.coe_nonneg)) (mul_nonneg hR hT))
  change ‖e t‖ ≤ _
  apply hout.trans_eq
  dsimp only [R]
  calc
    _ = A*T*|y-x|^2*(Real.exp (2*K*T)*Real.exp (K*T)) := by ring
    _ = _ := by
      rw [←Real.exp_add,show 2*K*T+K*T=3*K*T by ring]
      ring

theorem hasDerivAt_integral_flow_initial (b H : ℝ → ℝ → ℝ) (L K A : ℝ≥0)
    (hb : Paper.IsBoundedMeasurableDrift b L K)
    (hHm : Measurable (Function.uncurry H)) (hH : ∀ s z,‖H s z‖ ≤ K)
    (hder : ∀ s z,HasDerivAt (b s) (H s z) z)
    (hHL : ∀ s,LipschitzWith A (H s))
    (T : ℝ) (hT : 0 ≤ T) (W : ℝ → ℝ) (X : ℝ → ℝ → ℝ)
    (hX : ∀ x,Continuous (X x))
    (hXe : ∀ x t,t∈Icc (0 : ℝ) T → X x t=x+W t+∫ s in 0..t,b s (X x s))
    (x t : ℝ) (ht : t∈Icc (0 : ℝ) T) :
    HasDerivAt (fun y => X y t) (Real.exp (∫ s in 0..t,H s (X x s))) x := by
  let C := A*T*Real.exp (3*K*T)
  have hC : 0 ≤ C := by dsimp only [C];positivity
  apply hasDerivAt_iff_tendsto.mpr
  apply squeeze_zero (fun _ => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
    (g := fun y : ℝ => C*|y-x|)
  · intro y
    have he := integral_flow_quadratic_error b H L K A hb hHm hH hder hHL T hT W X hX hXe x y t ht
    simp only [smul_eq_mul]
    apply (mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (norm_nonneg _))).trans
    dsimp only [C]
    by_cases h : y=x
    · simp [h]
    · rw [Real.norm_eq_abs]
      have hδ : |y-x| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr h)
      apply le_of_eq
      field_simp
  · have hlim : Tendsto (fun y : ℝ => C*|y-x|) (𝓝 x) (𝓝 (C*|x-x|)) :=
      ((show Continuous (fun y : ℝ => C*|y-x|) from
        continuous_const.mul ((continuous_id.sub continuous_const).abs)).continuousAt.tendsto)
    simpa only [sub_self,abs_zero,mul_zero] using hlim

end QuantitativeFollowup
