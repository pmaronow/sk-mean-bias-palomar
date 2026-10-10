module
public import QuantitativeFollowup.ScalarFlowCalculus
public import Paper.ParisiState
public import Mathlib.Analysis.Normed.Module.Convex

@[expose] public section

/-! Initial-data comparison and a genuine quadratic Taylor bound for
measurable-time integral ODEs. These are analytic foundations for the
actual scalar restart flow. -/
noncomputable section
open Set MeasureTheory Paper FourPapersCommon
open scoped NNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem integral_state_initial_bound (b : ℝ → ℝ → ℝ) (L K : ℝ≥0)
    (hb : Paper.IsBoundedMeasurableDrift b L K)
    (T : ℝ) (x y : ℝ) (W X Y : ℝ → ℝ) (hX : Continuous X) (hY : Continuous Y)
    (hXe : ∀ t∈Icc (0 : ℝ) T,X t=x+W t+∫ s in 0..t,b s (X s))
    (hYe : ∀ t∈Icc (0 : ℝ) T,Y t=y+W t+∫ s in 0..t,b s (Y s)) :
    ∀ t∈Icc (0 : ℝ) T,‖Y t-X t‖ ≤ |y-x| * Real.exp (K*t) := by
  let f := fun t => ‖Y t-X t‖
  have hfc : Continuous f := (hY.sub hX).norm
  have hi (U : ℝ → ℝ) (hU : Continuous U) (t : ℝ) :
      IntervalIntegrable (fun s => b s (U s)) volume 0 t :=
    intervalIntegrable_const.mono_fun'
      (hb.measurable.comp (measurable_id.prodMk hU.measurable)).aestronglyMeasurable
      (.of_forall fun s => hb.norm_le s _)
  have hineq (t : ℝ) (ht : t∈Icc (0 : ℝ) T) : f t ≤ |y-x| + K*(∫ s in 0..t,f s) := by
    have hm := intervalIntegral.integral_mono_on ht.1 ((hi Y hY t).sub (hi X hX t)).norm
      ((hfc.intervalIntegrable 0 t).const_mul (K : ℝ))
      (fun s _ => (hb.lipschitz s).norm_sub_le (Y s) (X s))
    have hn := (intervalIntegral.norm_integral_le_integral_norm ht.1
      (f := fun s => b s (Y s)-b s (X s))).trans hm
    rw [intervalIntegral.integral_const_mul] at hn
    change ‖Y t-X t‖ ≤ _
    rw [hYe t ht,hXe t ht,
      show (y+W t+∫ s in 0..t,b s (Y s))-(x+W t+∫ s in 0..t,b s (X s))=
        (y-x)+((∫ s in 0..t,b s (Y s))-(∫ s in 0..t,b s (X s))) by ring,
      ←intervalIntegral.integral_sub (hi Y hY t) (hi X hX t)]
    exact (norm_add_le _ _).trans (add_le_add (le_refl _) hn)
  exact le_exp_of_integral_le f hfc T |y-x| K (abs_nonneg _) K.coe_nonneg
    (fun _ _ => norm_nonneg _) hineq

theorem derivative_lipschitz_quadratic_remainder (f f' : ℝ → ℝ)
    (hf : ∀ x,HasDerivAt f (f' x) x) (A : ℝ≥0) (hA : LipschitzWith A f') (x y : ℝ) :
    ‖f y-f x-f' x*(y-x)‖ ≤ A*‖y-x‖^2 := by
  let R := fun z => f z-f x-f' x*(z-x)
  have hR (z : ℝ) : HasDerivAt R (f' z-f' x) z := by
    convert! ((hf z).sub_const (f x)).sub
      (((hasDerivAt_id z).sub_const x).const_mul (f' x)) using 1
    simp
  have hd (z : ℝ) (hz : z∈Metric.closedBall x ‖y-x‖) :
      ‖f' z-f' x‖ ≤ A*‖y-x‖ := by
    have hh := hA.norm_sub_le z x
    exact hh.trans (mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz)
      A.coe_nonneg)
  have hx : x∈Metric.closedBall x ‖y-x‖ := Metric.mem_closedBall_self (norm_nonneg _)
  have hy : y∈Metric.closedBall x ‖y-x‖ := by simp only [Metric.mem_closedBall,dist_eq_norm,le_refl]
  have hm := (convex_closedBall x ‖y-x‖).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (hR z).hasDerivWithinAt) hd hx hy
  simpa only [R,sub_self,mul_zero,sub_zero,pow_two,mul_assoc] using hm

end QuantitativeFollowup
