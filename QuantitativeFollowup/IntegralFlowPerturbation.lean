module
public import QuantitativeFollowup.IntegralFlowInitial

@[expose] public section

/-! A true time-L¹ perturbation bound for the constructed integral flow.
The comparison uses the changed drift along the fixed reference path. -/
noncomputable section
open Set MeasureTheory Paper FourPapersCommon
open scoped NNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 2200000

theorem integral_state_perturbation_bound (b c : ℝ → ℝ → ℝ) (L K : ℝ≥0)
    (hb : Paper.IsBoundedMeasurableDrift b L K) (hc : Paper.IsBoundedMeasurableDrift c L K)
    (T : ℝ) (hT : 0 ≤ T) (x y E : ℝ) (hE : 0 ≤ E)
    (W V X Y : ℝ → ℝ) (hX : Continuous X) (hY : Continuous Y)
    (hnoise : ∀ t∈Icc (0 : ℝ) T,‖V t-W t‖ ≤ E)
    (hXe : ∀ t∈Icc (0 : ℝ) T,X t=x+W t+∫ s in 0..t,b s (X s))
    (hYe : ∀ t∈Icc (0 : ℝ) T,Y t=y+V t+∫ s in 0..t,c s (Y s)) :
    ∀ t∈Icc (0 : ℝ) T,‖Y t-X t‖ ≤
      (|y-x|+E+(∫ s in 0..T,‖c s (X s)-b s (X s)‖))*Real.exp (K*t) := by
  let f := fun t => ‖Y t-X t‖
  let e := fun s => ‖c s (X s)-b s (X s)‖
  have hfc : Continuous f := (hY.sub hX).norm
  have hi (d : ℝ → ℝ → ℝ) (hd : Paper.IsBoundedMeasurableDrift d L K)
      (U : ℝ → ℝ) (hU : Continuous U) (t : ℝ) :
      IntervalIntegrable (fun s => d s (U s)) volume 0 t :=
    intervalIntegrable_const.mono_fun'
      (hd.measurable.comp (measurable_id.prodMk hU.measurable)).aestronglyMeasurable
      (.of_forall fun s => hd.norm_le s _)
  have hei (t : ℝ) : IntervalIntegrable e volume 0 t :=
    ((hi c hc X hX t).sub (hi b hb X hX t)).norm
  have hen : 0 ≤ ∫ s in 0..T,e s := intervalIntegral.integral_nonneg hT (fun _ _ => norm_nonneg _)
  have hineq (t : ℝ) (ht : t∈Icc (0 : ℝ) T) :
      f t ≤ (|y-x|+E+∫ s in 0..T,e s)+K*(∫ s in 0..t,f s) := by
    have hm := intervalIntegral.integral_mono_on ht.1
      ((hi c hc Y hY t).sub (hi b hb X hX t)).norm
      (((hfc.intervalIntegrable 0 t).const_mul (K : ℝ)).add (hei t))
      (fun s _ => (norm_sub_le_norm_sub_add_norm_sub (c s (Y s)) (c s (X s)) (b s (X s))).trans
        (add_le_add ((hc.lipschitz s).norm_sub_le (Y s) (X s)) le_rfl))
    have hn := (intervalIntegral.norm_integral_le_integral_norm ht.1
      (f := fun s => c s (Y s)-b s (X s))).trans hm
    rw [intervalIntegral.integral_add ((hfc.intervalIntegrable 0 t).const_mul (K : ℝ)) (hei t),
      intervalIntegral.integral_const_mul] at hn
    have heT := intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (Filter.Eventually.of_forall (fun s => norm_nonneg (c s (X s)-b s (X s)))) (hei T)
    change ‖Y t-X t‖ ≤ _
    rw [hYe t ht,hXe t ht,
      show (y+V t+∫ s in 0..t,c s (Y s))-(x+W t+∫ s in 0..t,b s (X s))=
        ((y-x)+(V t-W t))+((∫ s in 0..t,c s (Y s))-(∫ s in 0..t,b s (X s))) by ring,
      ←intervalIntegral.integral_sub (hi c hc Y hY t) (hi b hb X hX t)]
    have hh := (norm_add_le ((y-x)+(V t-W t)) (∫ s in 0..t,c s (Y s)-b s (X s))).trans
      (add_le_add ((norm_add_le (y-x) (V t-W t)).trans
        (add_le_add (le_refl ‖y-x‖) (hnoise t ht))) hn)
    change (∫ s in 0..t,e s) ≤ ∫ s in 0..T,e s at heT
    exact hh.trans (by rw [Real.norm_eq_abs]; linarith)
  exact le_exp_of_integral_le f hfc T _ K (by positivity) K.coe_nonneg
    (fun _ _ => norm_nonneg _) hineq

end QuantitativeFollowup
