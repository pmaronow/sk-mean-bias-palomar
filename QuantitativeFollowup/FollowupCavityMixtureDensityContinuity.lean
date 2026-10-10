module
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! Normalized positive densities vary in L1 under genuine pointwise
convergence. This proves bounded moving-observable continuity without an
unproved uniform density envelope. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1200000
variable {X A : Type*} [MeasurableSpace X] {μ : Measure X}
  [TopologicalSpace A] [FirstCountableTopology A]

theorem cavityDensity_integral_norm_sub_tendsto
    (ρ : A→X→ℝ) (a0 : A) (hi : ∀a,Integrable (ρ a) μ)
    (hpos : ∀a x,0≤ρ a x) (hmass : ∀a,(∫x,ρ a x∂μ)=1)
    (hc : ∀x,ContinuousAt (fun a=>ρ a x) a0) :
    Tendsto (fun a=>∫x,‖ρ a x-ρ a0 x‖∂μ) (𝓝 a0) (𝓝 0) := by
  have hm(a):Integrable (fun x=>min (ρ a x) (ρ a0 x)) μ :=
    (hi a0).mono' (continuous_min.comp_aestronglyMeasurable ((hi a).aestronglyMeasurable.prodMk (hi a0).aestronglyMeasurable))
      (.of_forall fun x=>by rw [Real.norm_of_nonneg (le_min (hpos a x) (hpos a0 x))];exact min_le_right _ _)
  have ht : Tendsto (fun a=>∫x,min (ρ a x) (ρ a0 x)∂μ) (𝓝 a0) (𝓝 1) :=by
    simpa only [min_self,hmass] using
      (tendsto_integral_filter_of_dominated_convergence (ρ a0)
        (.of_forall fun a=>(hm a).aestronglyMeasurable)
        (.of_forall fun a=>.of_forall fun x=>by
          rw [Real.norm_of_nonneg (le_min (hpos a x) (hpos a0 x))]
          exact min_le_right _ _) (hi a0)
        (.of_forall fun x=>(hc x).min continuousAt_const))
  have he(a):(∫x,‖ρ a x-ρ a0 x‖∂μ)=2-2*(∫x,min (ρ a x) (ρ a0 x)∂μ) :=by
    have hp(x):‖ρ a x-ρ a0 x‖=ρ a x+ρ a0 x-2*min (ρ a x) (ρ a0 x) :=by
      rw [Real.norm_eq_abs]
      rcases le_total (ρ a x) (ρ a0 x) with h|h
      · rw [min_eq_left h,abs_of_nonpos (sub_nonpos.mpr h)];ring
      · rw [min_eq_right h,abs_of_nonneg (sub_nonneg.mpr h)];ring
    simp_rw [hp]
    change (∫x,(ρ a+ρ a0) x-(fun y=>2*min (ρ a y) (ρ a0 y)) x∂μ)=_
    rw [integral_sub ((hi a).add (hi a0)) ((hm a).const_mul 2)]
    simp only [Pi.add_apply]
    rw [integral_add (hi a) (hi a0),integral_const_mul,hmass,hmass]
    norm_num
  simp_rw [he]
  simpa using (tendsto_const_nhds (x:=(2:ℝ))).sub (ht.const_mul 2)

theorem continuousAt_cavityDensity_bounded_moving_integral
    (ρ f : A→X→ℝ) (a0 : A) (hi : ∀a,Integrable (ρ a) μ)
    (hpos : ∀a x,0≤ρ a x) (hmass : ∀a,(∫x,ρ a x∂μ)=1)
    (hc : ∀x,ContinuousAt (fun a=>ρ a x) a0)
    (hf : ∀a,AEStronglyMeasurable (f a) μ) (hfc : ∀x,ContinuousAt (fun a=>f a x) a0)
    (B : ℝ) (hB : 0≤B) (hb : ∀a x,‖f a x‖≤B) :
    ContinuousAt (fun a=>∫x,ρ a x*f a x∂μ) a0 :=by
  have hif(a):Integrable (fun x=>ρ a x*f a x) μ:=
    ((hi a).mul_const B).mono' ((hi a).aestronglyMeasurable.mul (hf a))
      (.of_forall fun x=>by rw [norm_mul,Real.norm_of_nonneg (hpos a x)];exact mul_le_mul_of_nonneg_left (hb a x) (hpos a x))
  have hD(a):Integrable (fun x=>ρ a0 x*(f a x-f a0 x)) μ:=
    ((hi a0).mul_const (2*B)).mono' ((hi a0).aestronglyMeasurable.mul ((hf a).sub (hf a0)))
      (.of_forall fun x=>by
        rw [norm_mul,Real.norm_of_nonneg (hpos a0 x)]
        apply mul_le_mul_of_nonneg_left _ (hpos a0 x)
        exact (norm_sub_le _ _).trans (by linarith [hb a x,hb a0 x]))
  have hE(a):Integrable (fun x=>(ρ a x-ρ a0 x)*f a x) μ:=
    (((hi a).sub (hi a0)).norm.mul_const B).mono'
      (((hi a).aestronglyMeasurable.sub (hi a0).aestronglyMeasurable).mul (hf a))
      (.of_forall fun x=>by rw [norm_mul];exact mul_le_mul_of_nonneg_left (hb a x) (norm_nonneg _))
  have htD : Tendsto (fun a=>∫x,ρ a0 x*(f a x-f a0 x)∂μ) (𝓝 a0) (𝓝 0) :=by
    simpa only [sub_self,mul_zero,integral_zero] using
      (tendsto_integral_filter_of_dominated_convergence (fun x=>ρ a0 x*(2*B)) (f:=fun _=>0)
        (.of_forall fun a=>(hD a).aestronglyMeasurable)
        (.of_forall fun a=>.of_forall fun x=>by
          rw [norm_mul,Real.norm_of_nonneg (hpos a0 x)]
          exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (by linarith [hb a x,hb a0 x])) (hpos a0 x))
        ((hi a0).mul_const (2*B))
        (.of_forall fun x=>by
          simpa only [Pi.mul_def,Pi.sub_def,sub_self,mul_zero] using
            ((continuousAt_const (y:=ρ a0 x)).mul
              ((hfc x).sub (continuousAt_const (y:=f a0 x)))).tendsto))
  have htE : Tendsto (fun a=>∫x,(ρ a x-ρ a0 x)*f a x∂μ) (𝓝 a0) (𝓝 0) :=by
    apply squeeze_zero_norm (fun a=>?_) (show Tendsto
      (fun a=>B*(∫x,‖ρ a x-ρ a0 x‖∂μ)) (𝓝 a0) (𝓝 0) from by
        simpa only [mul_zero] using (cavityDensity_integral_norm_sub_tendsto ρ a0 hi hpos hmass hc).const_mul B)
    rw [←integral_const_mul]
    apply norm_integral_le_of_norm_le (((hi a).sub (hi a0)).norm.const_mul B)
    exact .of_forall fun x=>by
      rw [norm_mul]
      simpa only [Pi.sub_apply,mul_comm] using
        mul_le_mul_of_nonneg_left (hb a x) (norm_nonneg (ρ a x-ρ a0 x))
  have he(a):(∫x,ρ a x*f a x∂μ)-(∫x,ρ a0 x*f a0 x∂μ)=
      (∫x,(ρ a x-ρ a0 x)*f a x∂μ)+(∫x,ρ a0 x*(f a x-f a0 x)∂μ) :=by
    rw [←integral_sub (hif a) (hif a0),←integral_add (hE a) (hD a)]
    congr 1
    funext x
    ring
  have ht : Tendsto (fun a=>(∫x,ρ a x*f a x∂μ)-(∫x,ρ a0 x*f a0 x∂μ)) (𝓝 a0) (𝓝 0) :=by
    simpa only [he,zero_add] using htE.add htD
  change Tendsto (fun a=>∫x,ρ a x*f a x∂μ) (𝓝 a0) (𝓝 (∫x,ρ a0 x*f a0 x∂μ))
  simpa only [sub_add_cancel,zero_add] using ht.add_const (∫x,ρ a0 x*f a0 x∂μ)

end QuantitativeFollowup
