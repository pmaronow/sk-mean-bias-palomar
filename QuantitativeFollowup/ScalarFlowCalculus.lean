module
public import FourPapersCommon.IntegralGronwall
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-! Linear flow equations with genuinely measurable time coefficients.
The exponential primitive is proved to solve its Volterra equation by
the absolutely-continuous FTC, including all coefficient jumps. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem bounded_primitive_lipschitz (c : ℝ → ℝ) (hc : Measurable c)
    (K : ℝ≥0) (hK : ∀ t,‖c t‖ ≤ K) :
    LipschitzWith K (fun t => ∫ s in 0..t,c s) := by
  have hi (a b : ℝ) : IntervalIntegrable c volume a b :=
    intervalIntegrable_const.mono_fun' hc.aestronglyMeasurable (.of_forall hK)
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [dist_eq_norm,intervalIntegral.integral_interval_sub_left (hi 0 u) (hi 0 v),Real.dist_eq]
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => hK t)

theorem exp_primitive_volterra (c : ℝ → ℝ) (hc : Measurable c)
    (K : ℝ≥0) (hK : ∀ t,‖c t‖ ≤ K) (T : ℝ) (hT : 0 ≤ T) :
    ∀ t∈Icc (0 : ℝ) T,
      Real.exp (∫ s in 0..t,c s)=1+
        ∫ s in 0..t,c s*Real.exp (∫ u in 0..s,c u) := by
  let P : ℝ → ℝ := fun t => ∫ s in 0..t,c s
  let E : ℝ → ℝ := fun t => Real.exp (P t)
  have hi (a b : ℝ) : IntervalIntegrable c volume a b :=
    intervalIntegrable_const.mono_fun' hc.aestronglyMeasurable (.of_forall hK)
  have hP : LipschitzWith K P := bounded_primitive_lipschitz c hc K hK
  have hPb (s : ℝ) (hs : s∈Icc (0 : ℝ) T) : P s ≤ K*T := by
    have hn := hP.dist_le_mul s 0
    simp only [P,intervalIntegral.integral_same,Real.dist_eq,sub_zero,abs_of_nonneg hs.1] at hn
    exact (le_abs_self _).trans (hn.trans (mul_le_mul_of_nonneg_left hs.2 K.coe_nonneg))
  have hEL : LipschitzOnWith ((Real.exp (K*T)*K).toNNReal) E (Icc (0 : ℝ) T) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro s hs t ht
    have hps := hPb s hs
    have hpt := hPb t ht
    have hexp := (convex_Iic (K*T)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      (fun x hx => by simpa only [Real.norm_of_nonneg (Real.exp_pos x).le] using
        Real.exp_le_exp.mpr hx) hpt hps
    have hpdist := hP.dist_le_mul s t
    rw [dist_eq_norm] at hpdist
    rw [dist_eq_norm]
    change ‖Real.exp (P s)-Real.exp (P t)‖ ≤ _
    apply hexp.trans
    simpa only [Real.coe_toNNReal _ (by positivity : 0 ≤ Real.exp (K*T)*K),mul_assoc] using
      mul_le_mul_of_nonneg_left hpdist (Real.exp_pos (K*T)).le
  have hEac : AbsolutelyContinuousOnInterval E 0 T := by
    rw [←uIcc_of_le hT] at hEL
    exact hEL.absolutelyContinuousOnInterval
  have hde : ∀ᵐ s : ℝ,s∈Icc (0 : ℝ) T → deriv E s=c s*E s := by
    filter_upwards [(hi 0 T).ae_hasDerivAt_integral] with s hd hs
    have hsU : s∈uIcc (0 : ℝ) T := by rwa [uIcc_of_le hT]
    have hh := (Real.hasDerivAt_exp (P s)).comp s (hd hsU 0 (left_mem_uIcc))
    simpa only [E,P,mul_comm,Function.comp_def] using hh.deriv
  intro t ht
  have hac : AbsolutelyContinuousOnInterval E 0 t := hEac.mono (by
    rw [uIcc_of_le ht.1,uIcc_of_le hT]
    exact Icc_subset_Icc le_rfl ht.2)
  have heq : (∫ s in 0..t,c s*E s)=E t-E 0 := by
    calc
      _ = ∫ s in 0..t,deriv E s := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hde] with s hd hs
        rw [uIoc_of_le ht.1] at hs
        exact (hd ⟨hs.1.le,hs.2.trans ht.2⟩).symm
      _ = _ := hac.integral_deriv_eq_sub
  change E t=1+∫ s in 0..t,c s*E s
  rw [heq]
  simp only [E,P,intervalIntegral.integral_same,Real.exp_zero]
  ring

end QuantitativeFollowup
