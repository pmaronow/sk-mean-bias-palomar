module
public import QuantitativeFollowup.ScalarRegroupedContinuity
public import QuantitativeFollowup.ScalarResponseOperator

@[expose] public section

/-! Exact regrouping of the literal scalar response. Strict-future mass is
computed using the right CDF, and the marked spin is integrated under its
actual terminal conditional law. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon FRSB QuantitativePaper
open scoped Topology ENNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

 theorem parisiFreeMeasure_real_Ioi (μ : Paper.ParisiMeasure) (s : ℝ)
    (hs : s∈Icc (0 : ℝ) 1) (hμ : μ∈scalarFloor s) (p : Paper.Overlap) :
    (parisiFreeMeasure μ s).real (Ioi p)=1-parisiCDF μ p := by
  have hCDF : (parisiFreeMeasure μ s).real (Iic p)=parisiCDF μ p-s := by
    change (parisiFreeMeasure μ s (Iic p)).toReal=_
    rw [show Iic p={q : Paper.Overlap | (q : ℝ) ≤ p} by ext q; rfl,
      parisiFreeMeasure_cdf μ s p hs hμ p.property,
      ENNReal.toReal_ofReal (sub_nonneg.mpr (scalarFloor_cdf_lower hμ p.property.1))]
  have hc := measureReal_add_measureReal_compl (μ := parisiFreeMeasure μ s) (s := Iic p) measurableSet_Iic
  rw [compl_Iic] at hc
  have htot : (parisiFreeMeasure μ s).real univ=1-s := by
    rw [Measure.real,parisiFreeMeasure_univ,ENNReal.toReal_ofReal (by linarith [hs.2])]
  rw [hCDF,htot] at hc
  linarith

 theorem integral_strict_future_difference (ν : Measure Paper.Overlap) [IsFiniteMeasure ν]
    (p : Paper.Overlap) (a : ℝ) (f : Paper.Overlap → ℝ) (hf : Integrable f ν) :
    (∫ r,if p<r then a-f r else 0 ∂ν)=ν.real (Ioi p)*a-∫ r in Ioi p,f r ∂ν := by
  have he : (fun r : Paper.Overlap => if p<r then a-f r else 0)=
      (Ioi p).indicator (fun r => a-f r) := by funext r; rfl
  rw [he,integral_indicator measurableSet_Ioi,
    integral_sub (integrable_const _).integrableOn hf.integrableOn,
    setIntegral_const,smul_eq_mul]

 theorem integrable_strict_future_difference (ν : Measure Paper.Overlap) [IsFiniteMeasure ν]
    (p : Paper.Overlap) (a : ℝ) (f : Paper.Overlap → ℝ) (hf : Integrable f ν) :
    Integrable (fun r => if p<r then a-f r else 0) ν := by
  exact ((integrable_const a).sub hf).indicator measurableSet_Ioi

 theorem scalarFutureDerivativePairing_eq_kernel (β : ℝ) (μ : Paper.ParisiMeasure)
    (p r : Paper.Overlap) (hpr : (p : ℝ) ≤ r) :
    scalarFutureDerivativePairing β μ p r=scalarResponseKernel2 β μ p r 0 := by
  simp only [scalarFutureDerivativePairing,dif_pos hpr,scalarResponseKernel2,
    scalarFutureSquareDerivativeExtended_eq β μ p r hpr]

 theorem scalarFutureCenteredPairing_eq_kernel (β : ℝ) (μ : Paper.ParisiMeasure)
    (p r ell : Paper.Overlap) (hrl : (r : ℝ) ≤ ell) :
    scalarFutureCenteredPairing β μ p r ell=scalarResponseKernel7 β μ p r ell := by
  simp only [scalarFutureCenteredPairing,dif_pos hrl,scalarResponseKernel7,
    scalarFutureSquareExtended_eq β μ r ell hrl,scalarFutureSquareProcess]

 theorem scalarResponseKernel4_eq_marked (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (p r ell : Paper.Overlap) :
    (∫ z,scalarCenteredSquare β μ p z.1*Paper.spinSign z.2*M β μ r z.1
      ∂scalarMarkedSpinLaw β hβ μ)=scalarResponseKernel4 β μ p r ell := by
  have hf : Measurable (fun ω => scalarCenteredSquare β μ p ω*M β μ r ω) :=
    (((measurable_M β μ p p.property).pow_const 2).sub measurable_const).mul
      (measurable_M β μ r r.property)
  have hb : ∀ ω,‖scalarCenteredSquare β μ p ω*M β μ r ω‖ ≤ 1 := fun ω => by
    rw [norm_mul]
    exact (mul_le_mul (scalarCenteredSquare_norm_le_one β μ p ω)
      (scalar_M_norm_le_one β μ r ω) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have he := integral_scalarMarkedSpinLaw_terminal_sign β hβ μ _ hf 1 hb
  change (∫ z,_ ∂scalarMarkedSpinLaw β hβ μ)=(∫ ω,_ ∂canonicalBrownianMeasure)
  convert! he using 1 <;> congr 1 <;> funext z <;> ring

 theorem scalarResponseKernel_integrable_mul {ν : Measure Paper.Overlap} [IsFiniteMeasure ν]
    (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure) (p : Paper.Overlap)
    (F : Paper.Overlap → ℝ) (hF : Continuous F)
    (K : ℝ → Paper.ParisiMeasure → Paper.Overlap → Paper.Overlap → Paper.Overlap → ℝ)
    (hK : Continuous (fun z : ScalarResponseKernelParameters => K β z.1 z.2.1 z.2.2.1 z.2.2.2)) :
    Integrable (fun r => K β μ p r 0*F r) ν := by
  have harg : Continuous (fun r : Paper.Overlap => (μ,(p,(r,0))) : Paper.Overlap → ScalarResponseKernelParameters) := by fun_prop
  have h : Continuous (fun r : Paper.Overlap => K β μ p r 0*F r) := by
    convert! (hK.comp harg).mul hF using 1
  simpa only [IntegrableOn,Measure.restrict_univ] using
    h.continuousOn.integrableOn_compact (μ := ν) isCompact_univ

 theorem integral_scalarResponsePsi1 (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (s : ℝ) (hs : s∈Icc (0 : ℝ) 1) (hμ : μ∈scalarFloor s)
    (φ : C(Paper.Overlap,ℝ)) (p : Paper.Overlap) :
    (∫ r,scalarResponsePsi1 β μ φ p r ∂parisiFreeMeasure μ s)=
    2*(1-parisiCDF μ p)*scalarResponseKernel1 β μ p p 0*φ p
    -(∫ r in Ioi p,scalarResponseKernel2 β μ p r 0*φ r ∂parisiFreeMeasure μ s)
    -2*(∫ r,scalarResponseKernel3 β μ p r 0*φ (min p r) ∂parisiFreeMeasure μ s)
    -(∫ r,scalarResponseKernel4 β μ p r 0*φ r ∂parisiFreeMeasure μ s)
    +(1/2:ℝ)*(∫ r,scalarResponseKernel5 β μ p r 0*φ r ∂parisiFreeMeasure μ s) := by
  let ν := parisiFreeMeasure μ s
  have hi2 := scalarResponseKernel_integrable_mul (ν := ν) β hβ μ p φ φ.continuous
    scalarResponseKernel2 (continuous_scalarResponseKernel2 β hβ)
  have hi3 := scalarResponseKernel_integrable_mul (ν := ν) β hβ μ p (fun r => φ (min p r))
    (φ.continuous.comp (by fun_prop)) scalarResponseKernel3 (continuous_scalarResponseKernel3 β hβ)
  have hi4 := scalarResponseKernel_integrable_mul (ν := ν) β hβ μ p φ φ.continuous
    scalarResponseKernel4 (continuous_scalarResponseKernel4 β hβ)
  have hi5 := scalarResponseKernel_integrable_mul (ν := ν) β hβ μ p φ φ.continuous
    scalarResponseKernel5 (continuous_scalarResponseKernel5 β hβ)
  have hib := integrable_strict_future_difference ν p
    (2*scalarResponseKernel1 β μ p p 0*φ p) _ hi2
  have he := integral_strict_future_difference ν p
    (2*scalarResponseKernel1 β μ p p 0*φ p) _ hi2
  have hex : (fun r => scalarResponsePsi1 β μ φ p r)=
      (fun r => (if p<r then 2*scalarResponseKernel1 β μ p p 0*φ p-
          scalarResponseKernel2 β μ p r 0*φ r else 0)
        -2*(scalarResponseKernel3 β μ p r 0*φ (min p r))
        -scalarResponseKernel4 β μ p r 0*φ r+(1/2:ℝ)*(scalarResponseKernel5 β μ p r 0*φ r)) := by
    funext r
    simp only [scalarResponsePsi1,scalarResponseKernel1]
    ring
  dsimp only [ν] at hib hi2 hi3 hi4 hi5 he
  have ha := integral_add ((hib.sub (hi3.const_mul 2)).sub hi4) (hi5.const_mul (1/2:ℝ))
  have hs1 := integral_sub (hib.sub (hi3.const_mul 2)) hi4
  have hs2 := integral_sub hib (hi3.const_mul 2)
  simp only [Pi.add_apply,Pi.sub_apply] at ha hs1 hs2
  rw [hex,ha,hs1,hs2,integral_const_mul,integral_const_mul,he]
  rw [show ν.real (Ioi p)=1-parisiCDF μ p from parisiFreeMeasure_real_Ioi μ s hs hμ p]
  ring

 theorem integral_strict_future_sub_constant (ν : Measure Paper.Overlap) [IsFiniteMeasure ν]
    (p : Paper.Overlap) (a : ℝ) (f : Paper.Overlap → ℝ) (hf : Integrable f ν) :
    (∫ r,if p<r then f r-a else 0 ∂ν)=(∫ r in Ioi p,f r ∂ν)-ν.real (Ioi p)*a := by
  have he : (fun r : Paper.Overlap => if p<r then f r-a else 0)=
      (Ioi p).indicator (fun r => f r-a) := by funext r; rfl
  rw [he,integral_indicator measurableSet_Ioi,
    integral_sub hf.integrableOn (integrable_const _).integrableOn,
    setIntegral_const,smul_eq_mul]

 theorem integral_scalarResponsePsi2_inner (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (s : ℝ) (φ : C(Paper.Overlap,ℝ)) (p r : Paper.Overlap) :
    (∫ ell,scalarResponsePsi2 β μ φ p r ell ∂parisiFreeMeasure μ s)=
      (1/2:ℝ)*(∫ ell,scalarResponseKernel6 β μ p r ell*φ (min r ell) ∂parisiFreeMeasure μ s)
      +(1/2:ℝ)*((∫ ell in Ioi r,scalarResponseKernel7 β μ p r ell*φ ell ∂parisiFreeMeasure μ s)
        -(parisiFreeMeasure μ s).real (Ioi r)*(scalarResponseKernel5 β μ p r r*φ r)) := by
  let ν := parisiFreeMeasure μ s
  have harg : Continuous (fun ell : Paper.Overlap => (μ,(p,(r,ell))) : Paper.Overlap → ScalarResponseKernelParameters) := by fun_prop
  have hc6 : Continuous (fun ell : Paper.Overlap => scalarResponseKernel6 β μ p r ell*φ (min r ell)) := by
    convert! ((continuous_scalarResponseKernel6 β hβ).comp harg).mul (φ.continuous.comp (show Continuous (fun ell : Paper.Overlap => min r ell) by fun_prop)) using 1
  have hc7 : Continuous (fun ell : Paper.Overlap => scalarResponseKernel7 β μ p r ell*φ ell) := by
    convert! ((continuous_scalarResponseKernel7 β hβ).comp harg).mul φ.continuous using 1
  have hi6 : Integrable (fun ell => scalarResponseKernel6 β μ p r ell*φ (min r ell)) ν := by
    simpa only [IntegrableOn,Measure.restrict_univ] using hc6.continuousOn.integrableOn_compact (μ := ν) isCompact_univ
  have hi7 : Integrable (fun ell => scalarResponseKernel7 β μ p r ell*φ ell) ν := by
    simpa only [IntegrableOn,Measure.restrict_univ] using hc7.continuousOn.integrableOn_compact (μ := ν) isCompact_univ
  have hib : Integrable (fun ell => if r<ell then scalarResponseKernel7 β μ p r ell*φ ell-
      scalarResponseKernel5 β μ p r r*φ r else 0) ν :=
    (hi7.sub (integrable_const _)).indicator measurableSet_Ioi
  have hex : (fun ell => scalarResponsePsi2 β μ φ p r ell)=
      (fun ell => (1/2:ℝ)*(scalarResponseKernel6 β μ p r ell*φ (min r ell))+
        (1/2:ℝ)*(if r<ell then scalarResponseKernel7 β μ p r ell*φ ell-
          scalarResponseKernel5 β μ p r r*φ r else 0)) := by
    funext ell
    simp only [scalarResponsePsi2,scalarResponseKernel5]
    ring
  have ha := integral_add (hi6.const_mul (1/2:ℝ)) (hib.const_mul (1/2:ℝ))
  dsimp only [ν] at ha hi7
  rw [hex,ha,integral_const_mul,integral_const_mul,
    integral_strict_future_sub_constant _ r _ _ hi7]

 theorem integral_scalarResponsePsi2 (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (s : ℝ) (hs : s∈Icc (0 : ℝ) 1) (hμ : μ∈scalarFloor s)
    (φ : C(Paper.Overlap,ℝ)) (p : Paper.Overlap) :
    (∫ r,∫ ell,scalarResponsePsi2 β μ φ p r ell ∂parisiFreeMeasure μ s ∂parisiFreeMeasure μ s)=
      (1/2:ℝ)*(∫ r,∫ ell,scalarResponseKernel6 β μ p r ell*φ (min r ell)
        ∂parisiFreeMeasure μ s ∂parisiFreeMeasure μ s)
      +(1/2:ℝ)*(∫ r,∫ ell in Ioi r,scalarResponseKernel7 β μ p r ell*φ ell
        ∂parisiFreeMeasure μ s ∂parisiFreeMeasure μ s)
      -(1/2:ℝ)*(∫ r,(1-parisiCDF μ r)*(scalarResponseKernel5 β μ p r r*φ r)
        ∂parisiFreeMeasure μ s) := by
  let ν := parisiFreeMeasure μ s
  let F : Paper.Overlap → ℝ := fun r => ∫ ell,scalarResponsePsi2 β μ φ p r ell ∂ν
  let E : Paper.Overlap → ℝ := fun r => ∫ ell,scalarResponseKernel6 β μ p r ell*φ (min r ell) ∂ν
  let H : Paper.Overlap → ℝ := fun r => ∫ ell in Ioi r,scalarResponseKernel7 β μ p r ell*φ ell ∂ν
  let B : Paper.Overlap → ℝ := fun r => (1-parisiCDF μ r)*(scalarResponseKernel5 β μ p r r*φ r)
  have hF : Continuous F := by
    have hf : Continuous (fun z : Paper.Overlap×Paper.Overlap => scalarResponsePsi2 β μ φ p z.1 z.2) := by
      have harg : Continuous (fun z : Paper.Overlap×Paper.Overlap => (μ,(p,(z.1,z.2))) : _ → ScalarResponseKernelParameters) := by fun_prop
      convert! (continuous_scalarResponsePsi2 β hβ φ).comp harg using 1
    exact continuous_integral_parisiFreeMeasure_family s hs (fun _ => μ) continuous_const (fun _ => hμ) _ hf
  have hE : Continuous E := by
    have hf : Continuous (fun z : Paper.Overlap×Paper.Overlap => scalarResponseKernel6 β μ p z.1 z.2*φ (min z.1 z.2)) := by
      have harg : Continuous (fun z : Paper.Overlap×Paper.Overlap => (μ,(p,(z.1,z.2))) : _ → ScalarResponseKernelParameters) := by fun_prop
      convert! ((continuous_scalarResponseKernel6 β hβ).comp harg).mul
        (φ.continuous.comp (show Continuous (fun z : Paper.Overlap×Paper.Overlap => min z.1 z.2) by fun_prop)) using 1
    exact continuous_integral_parisiFreeMeasure_family s hs (fun _ => μ) continuous_const (fun _ => hμ) _ hf
  have hiF : Integrable F ν := by
    simpa only [IntegrableOn,Measure.restrict_univ] using hF.continuousOn.integrableOn_compact (μ := ν) isCompact_univ
  have hiE : Integrable E ν := by
    simpa only [IntegrableOn,Measure.restrict_univ] using hE.continuousOn.integrableOn_compact (μ := ν) isCompact_univ
  have hi5 := scalarResponseKernel_integrable_mul (ν := ν) β hβ μ p φ φ.continuous
    scalarResponseKernel5 (continuous_scalarResponseKernel5 β hβ)
  have hiB : Integrable B ν := by
    have hb : ∀ r : Paper.Overlap,‖1-parisiCDF μ r‖ ≤ (1 : ℝ) := fun r => by
      rw [Real.norm_eq_abs,abs_le]
      constructor <;> linarith [parisiCDF_nonneg μ r,parisiCDF_le_one μ r]
    exact hi5.bdd_mul (measurable_const.sub ((parisiCDF_measurable μ).comp measurable_subtype_coe)).aestronglyMeasurable (.of_forall hb)
  have he (r : Paper.Overlap) : F r=(1/2:ℝ)*E r+(1/2:ℝ)*(H r-B r) := by
    have hi := integral_scalarResponsePsi2_inner β hβ μ s φ p r
    rw [parisiFreeMeasure_real_Ioi μ s hs hμ r] at hi
    exact hi
  have heH : H=(fun r => 2*F r-E r+B r) := by funext r; linarith [he r]
  have hiH : Integrable H ν := by
    rw [heH]
    exact ((hiF.const_mul 2).sub hiE).add hiB
  have hex : F=(fun r => (1/2:ℝ)*E r+(1/2:ℝ)*(H r-B r)) := funext he
  change (∫ r,F r ∂ν)=(1/2:ℝ)*(∫ r,E r ∂ν)+(1/2:ℝ)*(∫ r,H r ∂ν)-(1/2:ℝ)*(∫ r,B r ∂ν)
  have ha := integral_add (hiE.const_mul (1/2:ℝ)) ((hiH.sub hiB).const_mul (1/2:ℝ))
  have hsub := integral_sub hiH hiB
  simp only [Pi.sub_apply] at ha hsub
  rw [hex,ha,integral_const_mul,integral_const_mul,hsub]
  ring

 theorem scalarResponseOperator_eq_kernels (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (s : ℝ) (φ : C(Paper.Overlap,ℝ)) (p : Paper.Overlap) :
    scalarResponseOperator β hβ μ s φ p=
    β^2*((scalarResponseKernel0 β μ p 0 0+2*(1-parisiCDF μ p)*scalarResponseKernel1 β μ p p 0)*φ p
      -(∫ r in Ioi p,scalarResponseKernel2 β μ p r 0*φ r ∂parisiFreeMeasure μ s)
      -2*(∫ r,scalarResponseKernel3 β μ p r 0*φ (min p r) ∂parisiFreeMeasure μ s)
      -(∫ r,scalarResponseKernel4 β μ p r 0*φ r ∂parisiFreeMeasure μ s)
      +(1/2:ℝ)*(∫ r,parisiCDF μ r*scalarResponseKernel5 β μ p r r*φ r ∂parisiFreeMeasure μ s)
      +(1/2:ℝ)*(∫ r,∫ ell,scalarResponseKernel6 β μ p r ell*φ (min r ell)
        ∂parisiFreeMeasure μ s ∂parisiFreeMeasure μ s)
      +(1/2:ℝ)*(∫ r,∫ ell in Ioi r,scalarResponseKernel7 β μ p r ell*φ ell
        ∂parisiFreeMeasure μ s ∂parisiFreeMeasure μ s)) := by
  have hi1 : Integrable (fun ω => M β μ p ω^2*C β μ p ω) canonicalBrownianMeasure := by
    apply (integrable_const (1 : ℝ)).mono'
      (((measurable_M β μ p p.property).pow_const 2).mul (measurable_C β hβ μ p.property)).aestronglyMeasurable
    exact .of_forall fun ω => scalarResponseKernel1_integrand_bound β μ p p 0 ω
  have he0 : (∫ ω,C β μ p ω^2+2*(1-parisiCDF μ p)*M β μ p ω^2*C β μ p ω ∂canonicalBrownianMeasure)=
      scalarResponseKernel0 β μ p 0 0+2*(1-parisiCDF μ p)*scalarResponseKernel1 β μ p p 0 := by
    have he : (fun ω => C β μ p ω^2+2*(1-parisiCDF μ p)*M β μ p ω^2*C β μ p ω)=
        (fun ω => C β μ p ω^2+(2*(1-parisiCDF μ p))*(M β μ p ω^2*C β μ p ω)) := by funext ω; ring
    rw [he,integral_add (integrable_C_sq β hβ μ p.property) (hi1.const_mul _),integral_const_mul]
    rfl
  have he2 : (∫ r in Ioi p,scalarFutureDerivativePairing β μ p r*φ r ∂parisiFreeMeasure μ s)=
      ∫ r in Ioi p,scalarResponseKernel2 β μ p r 0*φ r ∂parisiFreeMeasure μ s := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    rw [scalarFutureDerivativePairing_eq_kernel β μ p r (show (p : ℝ) ≤ r from hr.le)]
  have he7 (r : Paper.Overlap) : (∫ ell in Ioi r,scalarFutureCenteredPairing β μ p r ell*φ ell ∂parisiFreeMeasure μ s)=
      ∫ ell in Ioi r,scalarResponseKernel7 β μ p r ell*φ ell ∂parisiFreeMeasure μ s := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro ell hell
    dsimp only
    rw [scalarFutureCenteredPairing_eq_kernel β μ p r ell (show (r : ℝ) ≤ ell from hell.le)]
  unfold scalarResponseOperator
  rw [he0,he2]
  simp_rw [scalarResponseKernel4_eq_marked β hβ μ _ _ 0,he7]
  rfl

 theorem scalarResponseOperator_eq_regrouped (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (s : ℝ) (hs : s∈Icc (0 : ℝ) 1) (hμ : μ∈scalarFloor s)
    (φ : C(Paper.Overlap,ℝ)) (p : Paper.Overlap) :
    scalarResponseOperator β hβ μ s φ p=scalarRegroupedResponse β μ s φ p := by
  let ν := parisiFreeMeasure μ s
  have hi5 := scalarResponseKernel_integrable_mul (ν := ν) β hβ μ p φ φ.continuous
    scalarResponseKernel5 (continuous_scalarResponseKernel5 β hβ)
  have hb : ∀ r : Paper.Overlap,‖1-parisiCDF μ r‖ ≤ (1 : ℝ) := fun r => by
    rw [Real.norm_eq_abs,abs_le]
    constructor <;> linarith [parisiCDF_nonneg μ r,parisiCDF_le_one μ r]
  have hiT := hi5.bdd_mul (measurable_const.sub ((parisiCDF_measurable μ).comp measurable_subtype_coe)).aestronglyMeasurable (.of_forall hb)
  simp only [Pi.sub_apply,Function.comp_def] at hiT
  have heCDF : (∫ r,parisiCDF μ r*scalarResponseKernel5 β μ p r r*φ r ∂ν)=
      (∫ r,scalarResponseKernel5 β μ p r 0*φ r ∂ν)-
        ∫ r,(1-parisiCDF μ r)*(scalarResponseKernel5 β μ p r r*φ r) ∂ν := by
    have he : (fun r : Paper.Overlap => parisiCDF μ r*scalarResponseKernel5 β μ p r r*φ r)=
      (fun r => scalarResponseKernel5 β μ p r 0*φ r-
        (1-parisiCDF μ r)*(scalarResponseKernel5 β μ p r 0*φ r)) := by
      funext r
      simp only [scalarResponseKernel5]
      ring
    rw [he,integral_sub hi5 hiT]
    rfl
  rw [scalarResponseOperator_eq_kernels β hβ]
  unfold scalarRegroupedResponse
  rw [integral_scalarResponsePsi1 β hβ μ s hs hμ φ p,
    integral_scalarResponsePsi2 β hβ μ s hs hμ φ p]
  dsimp only [ν] at heCDF
  rw [heCDF]
  simp only [scalarResponseKernel0,scalarResponseKernel1]
  ring

end QuantitativeFollowup
