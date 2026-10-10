module
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic

@[expose] public section

/-! Time-L¹ convergence of one bounded factor and pointwise convergence
of the other imply convergence of their primitives at moving endpoints. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem bounded_product_primitive_tendsto {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (cn hn : ι → ℝ → ℝ) (c h : ℝ → ℝ)
    (hcn : ∀ i,Measurable (cn i)) (hhn : ∀ i,Measurable (hn i))
    (hc : Measurable c) (hh : Measurable h)
    (bcn : ∀ i s,‖cn i s‖ ≤ 1) (bhn : ∀ i s,‖hn i s‖ ≤ 1)
    (bc : ∀ s,‖c s‖ ≤ 1) (bh : ∀ s,‖h s‖ ≤ 1)
    (hC : Tendsto (fun i => ∫ s in 0..1,‖cn i s-c s‖) L (𝓝 0))
    (hH : ∀ s,Tendsto (fun i => hn i s) L (𝓝 (h s)))
    (tn : ι → ℝ) (t : ℝ) (htn : ∀ i,tn i∈Icc (0 : ℝ) 1)
    (ht : t∈Icc (0 : ℝ) 1) (hT : Tendsto tn L (𝓝 t)) :
    Tendsto (fun i => ∫ s in 0..tn i,cn i s*hn i s) L (𝓝 (∫ s in 0..t,c s*h s)) := by
  have hi (f : ℝ → ℝ) (hf : Measurable f) (bf : ∀ s,‖f s‖ ≤ 1) (a b : ℝ) :
      IntervalIntegrable f volume a b := intervalIntegrable_const.mono_fun'
        hf.aestronglyMeasurable (.of_forall bf)
  have hip (i : ι) (a b : ℝ) : IntervalIntegrable (fun s => cn i s*hn i s) volume a b :=
    hi (fun s => cn i s*hn i s) ((hcn i).mul (hhn i)) (fun s => by
      change ‖cn i s*hn i s‖ ≤ 1
      rw [norm_mul]
      exact (mul_le_mul (bcn i s) (bhn i s) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)) a b
  have hic (a b : ℝ) : IntervalIntegrable (fun s => c s*h s) volume a b :=
    hi (fun s => c s*h s) (hc.mul hh) (fun s => by
      change ‖c s*h s‖ ≤ 1
      rw [norm_mul]
      exact (mul_le_mul (bc s) (bh s) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)) a b
  have hHnorm : Tendsto (fun i => ∫ s in 0..1,‖hn i s-h s‖) L (𝓝 0) := by
    have he := tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Ioc (0 : ℝ) 1)) (fun _ => (2 : ℝ))
      (.of_forall fun i => ((hhn i).sub hh).norm.aestronglyMeasurable)
      (.of_forall fun i => .of_forall fun s => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact (norm_sub_le _ _).trans (by linarith [bhn i s,bh s])) (integrable_const _)
      (.of_forall fun s => by simpa only [Pi.sub_apply,sub_self,norm_zero] using ((hH s).sub_const (h s)).norm)
    simpa only [intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1),Pi.sub_apply,integral_zero] using he
  have hb (i : ι) : ‖(∫ s in 0..tn i,cn i s*hn i s)-(∫ s in 0..t,c s*h s)‖ ≤
      |tn i-t|+(∫ s in 0..1,‖cn i s-c s‖)+(∫ s in 0..1,‖hn i s-h s‖) := by
    have ha := intervalIntegral.integral_interval_sub_left (hip i 0 (tn i)) (hip i 0 t)
    have hfirst : ‖(∫ s in 0..tn i,cn i s*hn i s)-(∫ s in 0..t,cn i s*hn i s)‖ ≤ |tn i-t| := by
      rw [ha]
      simpa only [one_mul] using intervalIntegral.norm_integral_le_of_norm_le_const
        (a := t) (b := tn i) (C := (1 : ℝ)) (fun s _ => by
          rw [norm_mul]
          exact (mul_le_mul (bcn i s) (bhn i s) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
    have hdiff (s : ℝ) : ‖cn i s*hn i s-c s*h s‖ ≤ ‖cn i s-c s‖+‖hn i s-h s‖ := by
      rw [show cn i s*hn i s-c s*h s=(cn i s-c s)*hn i s+c s*(hn i s-h s) by ring]
      apply (norm_add_le _ _).trans
      rw [norm_mul,norm_mul]
      exact add_le_add (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (bhn i s) (norm_nonneg _))
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (bc s) (norm_nonneg _))
    have hdiffi (u v : ℝ) := ((hi _ (hcn i) (bcn i) u v).sub (hi _ hc bc u v)).norm.add
      (((hi _ (hhn i) (bhn i) u v).sub (hi _ hh bh u v)).norm)
    have hsecond : ‖(∫ s in 0..t,cn i s*hn i s)-(∫ s in 0..t,c s*h s)‖ ≤
        (∫ s in 0..1,‖cn i s-c s‖)+(∫ s in 0..1,‖hn i s-h s‖) := by
      rw [←intervalIntegral.integral_sub (hip i 0 t) (hic 0 t)]
      have hmono := intervalIntegral.integral_mono_on ht.1 ((hip i 0 t).sub (hic 0 t)).norm
        (hdiffi 0 t) (fun s _ => hdiff s)
      have hend := intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (.of_forall fun s => add_nonneg (norm_nonneg _) (norm_nonneg _)) (hdiffi 0 1)
      have hn := (intervalIntegral.norm_integral_le_integral_norm ht.1
        (f := fun s => cn i s*hn i s-c s*h s)).trans hmono |>.trans hend
      rw [intervalIntegral.integral_add ((hi _ (hcn i) (bcn i) 0 1).sub (hi _ hc bc 0 1)).norm
        (((hi _ (hhn i) (bhn i) 0 1).sub (hi _ hh bh 0 1)).norm)] at hn
      exact hn
    exact (norm_sub_le_norm_sub_add_norm_sub _ (∫ s in 0..t,cn i s*hn i s) _).trans
      ((add_le_add hfirst hsecond).trans_eq (by ring))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) hb
  simpa only [sub_self,abs_zero,zero_add] using ((hT.sub_const t).abs.add hC).add hHnorm

end QuantitativeFollowup
