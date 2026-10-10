module
public import QuantitativeFollowup.ScalarForwardWeight
public import QuantitativeFollowup.ScalarKernelBasics
public import FRSB.SupportQuotient
public import FRSB.FullSupport

@[expose] public section

/-! The actual scalar reference multiplier is one on the minimizing
support and decays exponentially throughout the remaining interval.
The decay uses the true conditional state law and actual forward density. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper FRSB
open scoped NNReal ENNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 2600000

theorem scalarGammaPrime_after_support_eq_sech (beta : ℝ) (hb : 0<beta)
    (μ : Paper.ParisiMeasure) (q t : ℝ) (hq : 0≤q)
    (hsupp : parisiSupport μ=Icc (0 : ℝ) q) (ht : t∈Icc q 1) :
    GammaPrime beta μ t=beta^2*
      (∫sample,sech (selectedParisiItoState beta 0 hb.ne' μ t.toNNReal sample)^4
        ∂canonicalBrownianMeasure) := by
  unfold GammaPrime curvatureMoment2
  congr 1
  apply integral_congr_ae
  filter_upwards with sample
  have ht0 : 0≤t := hq.trans ht.1
  have hstate : optimalStateReal beta μ sample t=
      selectedParisiItoState beta 0 hb.ne' μ t.toNNReal sample := by
    have he := optimalState_eq_real beta μ
      (t:=t.toNNReal) (by simpa only [Real.coe_toNNReal _ ht0] using ht.2) sample
    simpa only [optimalState_eq_selected beta hb.ne' μ,Real.coe_toNNReal _ ht0] using he.symm
  rw [C_eq_hessian,parisiHessian_after_support_interval beta hb μ q t _ hq hsupp ht,hstate]
  ring

theorem scalarGammaPrime_after_support_decay (beta : ℝ) (hb : 0<beta)
    (μ : Paper.ParisiMeasure) (q : ℝ) (hq : q∈Ioc (0 : ℝ) 1)
    (hsupp : parisiSupport μ=Icc (0 : ℝ) q) (t : ℝ) (ht : t∈Icc q 1) :
    GammaPrime beta μ t≤Real.exp (-beta^2*(t-q)/2)*GammaPrime beta μ q := by
  by_cases heq : t=q
  · subst t
    simp
  have hqt : q<t := lt_of_le_of_ne ht.1 (Ne.symm heq)
  let a := q.toNNReal
  let T := (t-q).toNNReal
  let v := (beta^2*(t-q)).toNNReal
  have hT : 0<T := Real.toNNReal_pos.mpr (sub_pos.mpr hqt)
  have hv : v≠0 := (Real.toNNReal_pos.mpr (mul_pos (sq_pos_of_pos hb) (sub_pos.mpr hqt))).ne'
  have ha : (a : ℝ)=q := Real.coe_toNNReal _ hq.1.le
  have hTr : (T : ℝ)=t-q := Real.coe_toNNReal _ (sub_nonneg.mpr hqt.le)
  have hsum : a+T=t.toNNReal := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add,ha,hTr,Real.coe_toNNReal _ (hq.1.le.trans ht.1)]
    ring
  have hvEq : (beta^2*(T : ℝ)).toNNReal=v := by rw [hTr]
  have he := selectedState_after_support_doob_expectation beta hb μ q hq.1.le hsupp a T
    (by rw [ha]) hT (by rw [ha,hTr];linarith [ht.2]) (fun y=>sech y^4)
    (continuous_sech.pow 4).measurable 1 (fun y=>by
      rw [Real.norm_of_nonneg (pow_nonneg (sech_pos y).le 4)]
      exact pow_le_one₀ (sech_pos y).le (sech_le_one y))
  rw [hsum,hvEq] at he
  have hDensity := integral_selectedState_bridgeDensity beta hb.ne' μ q hq
    (doobOperator v (fun y=>sech y^4)) (measurable_doobOperator v _ (continuous_sech.pow 4).measurable)
  have hDensityq := integral_selectedState_bridgeDensity beta hb.ne' μ q hq
    (fun y=>sech y^4) (continuous_sech.pow 4).measurable
  have hHeat := scalarForwardCoshWeight_doob_fourth_decay beta hb μ q q hq.1.le hsupp hq le_rfl v hv
  rw [←hDensity,←hDensityq] at hHeat
  have hm := mul_le_mul_of_nonneg_left hHeat (sq_nonneg beta)
  rw [scalarGammaPrime_after_support_eq_sech beta hb μ q t hq.1.le hsupp ht,
    scalarGammaPrime_after_support_eq_sech beta hb μ q q hq.1.le hsupp ⟨le_rfl,hq.2⟩,he]
  have hvR : (v : ℝ)=beta^2*(t-q) :=
    Real.coe_toNNReal _ (mul_nonneg (sq_nonneg beta) (sub_nonneg.mpr hqt.le))
  rw [hvR] at hm
  convert hm using 1 <;> ring

theorem scalar_reference_multiplier (beta : ℝ) (hbeta : 1<beta)
    (μ : Paper.ParisiMeasure) (hmin : IsParisiMinimizer beta 0 μ) :
    ∃q : ℝ,q∈Ioo (0 : ℝ) 1 ∧ parisiSupport μ=Icc (0 : ℝ) q ∧
      (∀t∈Icc (0 : ℝ) q,GammaPrime beta μ t=1) ∧
      (∀t∈Icc q 1,GammaPrime beta μ t≤Real.exp (-beta^2*(t-q)/2)) ∧
      (∀t∈Icc (0 : ℝ) 1,GammaPrime beta μ t≤1) := by
  have hb : 0<beta := zero_lt_one.trans hbeta
  obtain ⟨q,hq,hsupp⟩ := minimizer_full_support beta hbeta μ hmin
  have hUnit := GammaPrime_eq_one_on_support_interval beta hb.ne' μ hmin q hq.1 hq.2.le hsupp
  have hDecay : ∀t∈Icc q 1,GammaPrime beta μ t≤Real.exp (-beta^2*(t-q)/2) := by
    intro t ht
    have he := scalarGammaPrime_after_support_decay beta hb μ q ⟨hq.1,hq.2.le⟩ hsupp t ht
    simpa only [hUnit q ⟨hq.1.le,le_rfl⟩,mul_one] using he
  refine ⟨q,hq,hsupp,hUnit,hDecay,?_⟩
  intro t ht
  by_cases htq : t≤q
  · exact (hUnit t ⟨ht.1,htq⟩).le
  · exact (hDecay t ⟨le_of_not_ge htq,ht.2⟩).trans
      (Real.exp_le_one_iff.mpr (by
        have hp := mul_nonneg (sq_nonneg beta) (sub_nonneg.mpr (le_of_not_ge htq))
        linarith))

end QuantitativeFollowup
