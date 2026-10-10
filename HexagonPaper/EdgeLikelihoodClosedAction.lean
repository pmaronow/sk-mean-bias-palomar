module
public import HexagonPaper.EdgeLikelihoodPathKernel

@[expose] public section

/-! An atom-preserving closed-upper-endpoint form of the actual edge
log likelihood. It holds also for a zero-length edge. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup
open scoped Topology ENNReal
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
variable {n : ℕ}

theorem edgeStoppedAction_eq_closed_endpoints (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q h : Paper.Overlap) (hqh : q≤h)
    (Z : C(Paper.Overlap,AnisotropicParameter n)) :
    edgeStoppedAction D μ q h Z=
      Paper.parisiCDF μ q*anisotropicMeasureTailPotential D μ q (Z q)+
      (∫r in Ioc q h,anisotropicMeasureTailPotential D μ r (Z r) ∂(μ:Measure Paper.Overlap))+
      (μ:Measure Paper.Overlap).real (Ioi h)*anisotropicMeasureTailPotential D μ h (Z h) := by
  let F:=edgeNativePathPotential D μ Z
  let L:Paper.Overlap→ℝ:=(Iic q).indicator (fun _=>F q)
  let M:Paper.Overlap→ℝ:=(Ioc q h).indicator F
  let R:Paper.Overlap→ℝ:=(Ioi h).indicator (fun _=>F h)
  have hL : Integrable L (μ:Measure Paper.Overlap) :=
    (integrable_const _).indicator measurableSet_Iic
  have hM : Integrable M (μ:Measure Paper.Overlap) :=
    (continuousMap_integrable_probability F μ).indicator measurableSet_Ioc
  have hR : Integrable R (μ:Measure Paper.Overlap) :=
    (integrable_const _).indicator measurableSet_Ioi
  have he : (fun r=>edgeStoppedActionFunction D μ q h Z r)=fun r=>L r+M r+R r := by
    funext r
    by_cases hrq : r≤q
    · have hc : edgeIntervalClamp q h r=q := by
        apply Subtype.ext
        exact (congrArg (fun c : ℝ=>min c h) (max_eq_left hrq)).trans (min_eq_left hqh)
      have hM0 : r∉Ioc q h := fun hr=>not_lt_of_ge hrq hr.1
      have hR0 : r∉Ioi h := not_lt_of_ge (hrq.trans hqh)
      have hLm : r∈Iic q:=hrq
      simp only [edgeStoppedActionFunction_apply,hc,L,M,R,
        Set.indicator_of_mem hLm,Set.indicator_of_notMem hM0,
        Set.indicator_of_notMem hR0,add_zero,F,edgeNativePathPotential_apply]
    · have hqr : q<r := lt_of_not_ge hrq
      have hL0 : r∉Iic q:=hrq
      by_cases hrh : r≤h
      · have hc : edgeIntervalClamp q h r=r := by
          apply Subtype.ext
          exact (congrArg (fun c : ℝ=>min c h) (max_eq_right hqr.le)).trans (min_eq_left hrh)
        have hMm : r∈Ioc q h:=⟨hqr,hrh⟩
        have hR0 : r∉Ioi h:=not_lt_of_ge hrh
        simp only [edgeStoppedActionFunction_apply,hc,L,M,R,
          Set.indicator_of_notMem hL0,Set.indicator_of_mem hMm,
          Set.indicator_of_notMem hR0,zero_add,add_zero,F,edgeNativePathPotential_apply]
      · have hhr : h<r:=lt_of_not_ge hrh
        have hc : edgeIntervalClamp q h r=h := by
          apply Subtype.ext
          exact (congrArg (fun c : ℝ=>min c h) (max_eq_right hqr.le)).trans (min_eq_right hhr.le)
        have hM0 : r∉Ioc q h:=fun hr=>hrh hr.2
        have hRm : r∈Ioi h:=hhr
        simp only [edgeStoppedActionFunction_apply,hc,L,M,R,
          Set.indicator_of_notMem hL0,Set.indicator_of_notMem hM0,
          Set.indicator_of_mem hRm,zero_add,F,edgeNativePathPotential_apply]
  unfold edgeStoppedAction
  rw [he]
  change integral (μ:Measure Paper.Overlap) ((L+M)+R)=_
  rw [integral_add' (hL.add hM) hR,integral_add' hL hM]
  simp only [L,M,R,integral_indicator measurableSet_Iic,integral_indicator measurableSet_Ioc,
    integral_indicator measurableSet_Ioi,setIntegral_const,smul_eq_mul,F,edgeNativePathPotential_apply]
  rfl

theorem edgePathLogDensity_eq_closed_endpoints (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q h : Paper.Overlap) (hqh : q≤h)
    (Z : C(Paper.Overlap,AnisotropicParameter n)) :
    edgePathLogDensity D μ q h Z=
      Paper.parisiCDF μ h*anisotropicMeasureTailPotential D μ h (Z h)-
      Paper.parisiCDF μ q*anisotropicMeasureTailPotential D μ q (Z q)-
      ∫r in Ioc q h,anisotropicMeasureTailPotential D μ r (Z r) ∂(μ:Measure Paper.Overlap) := by
  rw [edgePathLogDensity,edgeStoppedAction_eq_closed_endpoints D μ q h hqh Z]
  have hm:=measureReal_add_measureReal_compl (μ:=(μ:Measure Paper.Overlap))
    (s:=Iic h) measurableSet_Iic
  have hm0 : Paper.parisiCDF μ h+(μ:Measure Paper.Overlap).real (Ioi h)=1:=by
    change (μ:Measure Paper.Overlap).real (Iic h)+(μ:Measure Paper.Overlap).real (Ioi h)=1
    simpa only [compl_Iic,probReal_univ] using hm
  have he:=congrArg (fun a:ℝ=>a*anisotropicMeasureTailPotential D μ h (Z h)) hm0
  simp only [add_mul,one_mul] at he
  linarith

end HexagonPaper
