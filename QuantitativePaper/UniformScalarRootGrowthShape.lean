module
public import QuantitativePaper.UniformScalarMild
public import QuantitativeFollowup.ScalarRootStrictness
public import FRSB.SupportQuotient
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-! Genuine shape of the energy-coordinate scalar jets: curvature decreases
on the positive half-line, its integral is bounded by the gradient range,
and contact forces a quantitatively nonzero third derivative somewhere. -/
noncomputable section
open Set MeasureTheory Filter Paper FRSB
open scoped Topology
namespace QuantitativePaper
set_option maxHeartbeats 1200000

theorem scalarEnergySpatialJet_one (β : ℝ) (μ : Paper.ParisiMeasure) (q x : ℝ) :
    scalarEnergySpatialJet β μ 1 (q,x)=β*parisiHessian β μ (q,β*x) := by
  change β^1*backwardD β μ 2 (q,β*x)=β*parisiHessian β μ (q,β*x)
  rw [backwardD_eq_spatialJet,parisiSpatialJet_two,pow_one]

theorem scalarEnergyJet_zero_origin (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (q : ℝ) (hq : q∈Icc (0:ℝ) 1) : scalarEnergySpatialJet β μ 0 (q,0)=0 := by
  simp only [scalarEnergySpatialJet_zero,mul_zero]
  exact parisiGradient_at_zero β hβ μ q hq

theorem scalarEnergyJet_two_nonpos (β : ℝ) (hβ : 0<β) (μ : Paper.ParisiMeasure)
    (q x : ℝ) (hq : q∈Icc (0:ℝ) 1) (hx : 0≤x) :
    scalarEnergySpatialJet β μ 2 (q,x)≤0 :=
  mul_nonpos_of_nonneg_of_nonpos (sq_nonneg β)
    (backwardD_three_nonpos β hβ.ne' μ q (β*x) hq (mul_nonneg hβ.le hx))

theorem scalarEnergyJet_two_origin (β : ℝ) (μ : Paper.ParisiMeasure)
    (q : ℝ) (hq : q∈Icc (0:ℝ) 1) : scalarEnergySpatialJet β μ 2 (q,0)=0 := by
  have he:=backwardD_reflect β μ q hq 3 0
  simp only [neg_zero] at he
  norm_num at he
  simp only [scalarEnergySpatialJet,mul_zero,Nat.reduceAdd]
  change β^2*backwardD β μ 3 (q,0)=0
  rw [show backwardD β μ 3 (q,0)=0 by linarith,mul_zero]

theorem scalarEnergyJet_one_reflect (β : ℝ) (μ : Paper.ParisiMeasure)
    (q x : ℝ) (hq : q∈Icc (0:ℝ) 1) :
    scalarEnergySpatialJet β μ 1 (q,-x)=scalarEnergySpatialJet β μ 1 (q,x) := by
  have he:=backwardD_reflect β μ q hq 2 (β*x)
  norm_num at he
  simpa only [scalarEnergySpatialJet,pow_one,Nat.reduceAdd,mul_neg,backwardD] using congrArg (fun a:ℝ=>β*a) he

theorem scalarEnergyJet_one_antitone (β : ℝ) (hβ : 0<β) (μ : Paper.ParisiMeasure)
    (q : ℝ) (hq : q∈Icc (0:ℝ) 1) :
    AntitoneOn (fun x=>scalarEnergySpatialJet β μ 1 (q,x)) (Ici (0:ℝ)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    ((continuous_scalarEnergySpatialJet β μ 1).comp (continuous_const.prodMk continuous_id)).continuousOn
  · intro x _
    exact (hasDerivAt_scalarEnergySpatialJet β μ 1 q x hq).differentiableAt.differentiableWithinAt
  · intro x hx
    change deriv (fun y=>scalarEnergySpatialJet β μ 1 (q,y)) x ≤ 0
    rw [(hasDerivAt_scalarEnergySpatialJet β μ 1 q x hq).deriv]
    exact scalarEnergyJet_two_nonpos β hβ μ q x hq (interior_subset hx)

theorem scalarEnergyJet_one_le_origin (β : ℝ) (hβ : 0<β) (μ : Paper.ParisiMeasure)
    (q x : ℝ) (hq : q∈Icc (0:ℝ) 1) :
    scalarEnergySpatialJet β μ 1 (q,x)≤ scalarEnergySpatialJet β μ 1 (q,0) := by
  by_cases hx : 0≤x
  · exact scalarEnergyJet_one_antitone β hβ μ q hq (by simp) hx hx
  · have hh:=scalarEnergyJet_one_antitone β hβ μ q hq (by simp)
      (show -x∈Ici (0:ℝ) by simp;linarith) (show 0≤-x by linarith)
    change scalarEnergySpatialJet β μ 1 (q,-x) ≤ scalarEnergySpatialJet β μ 1 (q,0) at hh
    rwa [scalarEnergyJet_one_reflect β μ q x hq] at hh

theorem scalarEnergyJet_one_at_four_le (β : ℝ) (hβ : 0<β) (μ : Paper.ParisiMeasure)
    (q : ℝ) (hq : q∈Icc (0:ℝ) 1) : scalarEnergySpatialJet β μ 1 (q,4)≤1/4 := by
  have hc : Continuous (fun x=>scalarEnergySpatialJet β μ 1 (q,x)):=
    (continuous_scalarEnergySpatialJet β μ 1).comp (continuous_const.prodMk continuous_id)
  have hFTC:=intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a:=(0:ℝ)) (b:=4) (fun x _=>hasDerivAt_scalarEnergySpatialJet β μ 0 q x hq)
    (hc.intervalIntegrable 0 4)
  have hlo:=intervalIntegral.integral_mono_on (by norm_num : (0:ℝ)≤4)
    (intervalIntegrable_const (μ:=volume) (c:=scalarEnergySpatialJet β μ 1 (q,4)))
    (hc.intervalIntegrable 0 4)
    (fun x hx=>scalarEnergyJet_one_antitone β hβ μ q hq hx.1 (by norm_num) hx.2)
  rw [intervalIntegral.integral_const] at hlo
  simp only [sub_zero,smul_eq_mul] at hlo
  rw [hFTC,scalarEnergyJet_zero_origin β hβ.ne' μ q hq,sub_zero] at hlo
  have hh:=(abs_le.mp (norm_scalarEnergySpatialJet_zero_le_one β μ (q,4))).2
  nlinarith

theorem scalarEnergyJet_one_origin_ge_contact (β : ℝ) (hβ : 0<β)
    (μ : Paper.ParisiMeasure) (q : ℝ) (hq : q∈Icc (0:ℝ) 1)
    (hcontact : GammaPrime β μ q=1) : 1≤ scalarEnergySpatialJet β μ 1 (q,0) := by
  have hh (ω : Paper.BrownianSample) : β^2*(C β μ q ω)^2≤(scalarEnergySpatialJet β μ 1 (q,0))^2 := by
    have hlo:=(C_pos β μ hq ω).le
    have hhi:=scalarEnergyJet_one_le_origin β hβ μ q (optimalStateReal β μ ω q/β) hq
    rw [scalarEnergySpatialJet_one] at hhi
    have he : β*(optimalStateReal β μ ω q/β)=optimalStateReal β μ ω q:=by field_simp
    rw [he,←C_eq_hessian] at hhi
    have hb : 0≤β*C β μ q ω:=mul_nonneg hβ.le hlo
    nlinarith
  have hi:=integral_mono ((integrable_C_sq β hβ.ne' μ hq).const_mul (β^2))
    (integrable_const ((scalarEnergySpatialJet β μ 1 (q,0))^2)) hh
  rw [integral_const_mul,integral_const] at hi
  simp only [probReal_univ,one_smul] at hi
  change GammaPrime β μ q≤(scalarEnergySpatialJet β μ 1 (q,0))^2 at hi
  rw [hcontact] at hi
  have hp : 0≤ scalarEnergySpatialJet β μ 1 (q,0):=by
    rw [scalarEnergySpatialJet_one,mul_zero]
    exact mul_nonneg hβ.le (parisiHessian_pos_all β μ q 0 hq).le
  nlinarith

theorem exists_scalarEnergy_third_large (β : ℝ) (hβ : 0<β) (μ : Paper.ParisiMeasure)
    (q : ℝ) (hq : q∈Icc (0:ℝ) 1)
    (hcontact : GammaPrime β μ q=1) :
    ∃x∈Ioo (0:ℝ) 4,3/16≤-scalarEnergySpatialJet β μ 2 (q,x) := by
  have hc : Continuous (fun x=>scalarEnergySpatialJet β μ 1 (q,x)):=
    (continuous_scalarEnergySpatialJet β μ 1).comp (continuous_const.prodMk continuous_id)
  obtain ⟨x,hx,hd⟩:=exists_hasDerivAt_eq_slope
    (fun x=>scalarEnergySpatialJet β μ 1 (q,x)) (fun x=>scalarEnergySpatialJet β μ 2 (q,x))
    (by norm_num : (0:ℝ)<4) hc.continuousOn (fun x _=>hasDerivAt_scalarEnergySpatialJet β μ 1 q x hq)
  have he:=hd
  have ho:=scalarEnergyJet_one_origin_ge_contact β hβ μ q hq hcontact
  have hf:=scalarEnergyJet_one_at_four_le β hβ μ q hq
  exact ⟨x,hx,by norm_num only [sub_zero] at he;nlinarith⟩

end QuantitativePaper
