module
public import HexagonPaper.EdgeLikelihoodStoppedAction
public import HexagonPaper.EdgeLikelihoodEndpoints
public import QuantitativeFollowup.ParisiFreeMeasure

@[expose] public section

/-! Exact arbitrary-endpoint version of the paper's open-edge likelihood.
The left endpoint uses the right CDF, the right endpoint the left CDF,
and the free profile has exactly the same open-edge restriction. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace HexagonPaper
open FourPapersCommon QuantitativePaper QuantitativeFollowup
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem edgeStoppedAction_eq_endpoint_atoms (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q h : Paper.Overlap) (hqh : q<h)
    (Z : C(Paper.Overlap,AnisotropicParameter n)) :
    edgeStoppedAction D μ q h Z=
      Paper.parisiCDF μ q*anisotropicMeasureTailPotential D μ q (Z q)+
      (∫r in Ioo q h,anisotropicMeasureTailPotential D μ r (Z r) ∂(μ:Measure Paper.Overlap))+
      (μ:Measure Paper.Overlap).real (Ici h)*anisotropicMeasureTailPotential D μ h (Z h) := by
  let F:=edgeNativePathPotential D μ Z
  let L:Paper.Overlap→ℝ:=(Iic q).indicator (fun _=>F q)
  let M:Paper.Overlap→ℝ:=(Ioo q h).indicator F
  let R:Paper.Overlap→ℝ:=(Ici h).indicator (fun _=>F h)
  have hL : Integrable L (μ:Measure Paper.Overlap) :=
    (integrable_const _).indicator measurableSet_Iic
  have hM : Integrable M (μ:Measure Paper.Overlap) :=
    (continuousMap_integrable_probability F μ).indicator measurableSet_Ioo
  have hR : Integrable R (μ:Measure Paper.Overlap) :=
    (integrable_const _).indicator measurableSet_Ici
  have he : (fun r=>edgeStoppedActionFunction D μ q h Z r)=fun r=>L r+M r+R r := by
    funext r
    by_cases hrq : r≤q
    · have hc : edgeIntervalClamp q h r=q := by
        apply Subtype.ext
        exact (congrArg (fun c : ℝ=>min c h) (max_eq_left hrq)).trans (min_eq_left hqh.le)
      have hM0 : r∉Ioo q h := fun hr=>not_lt_of_ge hrq hr.1
      have hR0 : r∉Ici h := not_le_of_gt (hrq.trans_lt hqh)
      have hLm : r∈Iic q:=hrq
      simp only [edgeStoppedActionFunction_apply,hc,L,M,R,
        Set.indicator_of_mem hLm,Set.indicator_of_notMem hM0,
        Set.indicator_of_notMem hR0,add_zero,F,edgeNativePathPotential_apply]
    · have hqr : q<r := lt_of_not_ge hrq
      have hL0 : r∉Iic q:=hrq
      by_cases hrh : r<h
      · have hc : edgeIntervalClamp q h r=r := by
          apply Subtype.ext
          exact (congrArg (fun c : ℝ=>min c h) (max_eq_right hqr.le)).trans (min_eq_left hrh.le)
        have hMm : r∈Ioo q h:=⟨hqr,hrh⟩
        have hR0 : r∉Ici h:=not_le_of_gt hrh
        simp only [edgeStoppedActionFunction_apply,hc,L,M,R,
          Set.indicator_of_notMem hL0,Set.indicator_of_mem hMm,
          Set.indicator_of_notMem hR0,zero_add,add_zero,F,edgeNativePathPotential_apply]
      · have hhr : h≤r:=le_of_not_gt hrh
        have hc : edgeIntervalClamp q h r=h := by
          apply Subtype.ext
          exact (congrArg (fun c : ℝ=>min c h) (max_eq_right hqr.le)).trans (min_eq_right hhr)
        have hM0 : r∉Ioo q h:=fun hr=>hrh hr.2
        have hRm : r∈Ici h:=hhr
        simp only [edgeStoppedActionFunction_apply,hc,L,M,R,
          Set.indicator_of_notMem hL0,Set.indicator_of_notMem hM0,
          Set.indicator_of_mem hRm,zero_add,F,edgeNativePathPotential_apply]
  unfold edgeStoppedAction
  rw [he]
  change integral (μ:Measure Paper.Overlap) ((L+M)+R)=_
  rw [integral_add' (hL.add hM) hR,integral_add' hL hM]
  simp only [L,M,R,integral_indicator measurableSet_Iic,integral_indicator measurableSet_Ioo,
    integral_indicator measurableSet_Ici,setIntegral_const,smul_eq_mul,F,edgeNativePathPotential_apply]
  rfl

theorem edgeLeftCDF_add_upper_mass (μ : Paper.ParisiMeasure) (h : Paper.Overlap) :
    edgeLeftCDF μ h+(μ:Measure Paper.Overlap).real (Ici h)=1 := by
  have he:=measureReal_add_measureReal_compl (μ:=(μ:Measure Paper.Overlap))
    (s:=Iio h) measurableSet_Iio
  simpa only [edgeLeftCDF,compl_Iio,probReal_univ] using he

theorem edgeStoppedLikelihood_eq_open_endpoints (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q h : Paper.Overlap) (hqh : q<h)
    (Z : C(Paper.Overlap,AnisotropicParameter n)) :
    edgeStoppedLikelihood D μ q h Z=ENNReal.ofReal (Real.exp (
      edgeLeftCDF μ h*anisotropicMeasureTailPotential D μ h (Z h)-
      Paper.parisiCDF μ q*anisotropicMeasureTailPotential D μ q (Z q)-
      ∫r in Ioo q h,anisotropicMeasureTailPotential D μ r (Z r) ∂(μ:Measure Paper.Overlap))) := by
  rw [edgeStoppedLikelihood,edgeStoppedAction_eq_endpoint_atoms D μ q h hqh Z]
  congr 2
  have hm:=congrArg (fun c : ℝ=>c*anisotropicMeasureTailPotential D μ h (Z h))
    (edgeLeftCDF_add_upper_mass μ h)
  simp only [add_mul,one_mul] at hm
  linarith

theorem edge_free_measure_open_restriction (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) (q h : Paper.Overlap) :
    (parisiFreeMeasure μ a).restrict (Ioo q h)=
      (μ:Measure Paper.Overlap).restrict (Ioo q h) := by
  have hz : zeroOverlap∉Ioo q h := by
    intro hr
    exact not_lt_of_ge q.property.1 hr.1
  have he:=congrArg (fun ν : Measure Paper.Overlap=>ν.restrict (Ioo q h))
    (root_add_parisiFreeMeasure μ a ha hμ)
  rw [Measure.restrict_add,Measure.restrict_smul,restrict_dirac,if_neg hz,
    smul_zero,zero_add] at he
  exact he

theorem edgeStoppedLikelihood_eq_printed_free_endpoints (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hμ : μ∈scalarFloor a) (q h : Paper.Overlap) (hqh : q<h)
    (Z : C(Paper.Overlap,AnisotropicParameter n)) :
    edgeStoppedLikelihood D μ q h Z=ENNReal.ofReal (Real.exp (
      edgeLeftCDF μ h*anisotropicMeasureTailPotential D μ h (Z h)-
      Paper.parisiCDF μ q*anisotropicMeasureTailPotential D μ q (Z q)-
      ∫r in Ioo q h,anisotropicMeasureTailPotential D μ r (Z r) ∂parisiFreeMeasure μ a)) := by
  rw [edgeStoppedLikelihood_eq_open_endpoints D μ q h hqh Z,
    edge_free_measure_open_restriction μ a ha hμ q h]

end HexagonPaper
