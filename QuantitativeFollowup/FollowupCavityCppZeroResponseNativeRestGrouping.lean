module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeResponseDefinitions
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteObservableGrouping
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteFiveGrouping
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeChargeMeans
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativePairSecondOldAverage
public import QuantitativeFollowup.FollowupCavityCppZeroResponseRestIntegrand
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteFreeLinearity

@[expose] public section

/-! The actual finite rest-observable group equals its complete native
Hessian/future-gradient integrand, pointwise on the marked whole path. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper FRSB
open scoped BigOperators
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
 theorem nativeRest_zero_mem : (0:ℝ)∈Icc 0 1:=⟨le_rfl,zero_le_one⟩

private theorem rest_mixed_hessian_sum (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (r p : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) :
    cavityZeroRestMixedHessian D μ r p sample=
      (∑i : Fin n,anisotropicProcessMagnetization D μ r sample i*
        ∑l : Fin n,anisotropicProcessMagnetization D μ p sample l*
          nativeAnisotropicProcessHessianMatrix D μ p sample l i)/(n:ℝ)^2:=by
  unfold cavityZeroRestMixedHessian
  rw [cavitySignedResponseMixedHessian_expand]
  simp_rw [cavitySignedResponseHessianMeanCoordinate_eq_matrix_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _=>mul_comm _ _

private theorem rest_trace_hessian_sum (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (p : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) :
    cavityZeroRestHessianSquare D μ p sample=
      (∑i : Fin n,∑l : Fin n,(nativeAnisotropicProcessHessianMatrix D μ p sample l i)^2)/(n:ℝ)^2:=by
  unfold cavityZeroRestHessianSquare
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro l _
  rw [nativeAnisotropicProcessHessianMatrix_symmetric D μ p sample i l]
  ring

private theorem weighted_basis_apply (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (p r : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) :
    (∑l : Fin n,anisotropicProcessMagnetization D μ p sample l*
      fderiv ℝ (fun x=>anisotropicRestartMeanSquare D μ sample.1 p x r)
        (anisotropicMeasureState D μ p sample) (EuclideanSpace.single l 1))=
      fderiv ℝ (fun x=>anisotropicRestartMeanSquare D μ sample.1 p x r)
        (anisotropicMeasureState D μ p sample) (anisotropicProcessMagnetization D μ p sample):=by
  have hv:anisotropicProcessMagnetization D μ p sample=
      ∑l : Fin n,anisotropicProcessMagnetization D μ p sample l •EuclideanSpace.single l 1:=by
    ext i
    simp [EuclideanSpace.single_apply,Pi.single_apply]
  calc
    _=fderiv ℝ (fun x=>anisotropicRestartMeanSquare D μ sample.1 p x r)
        (anisotropicMeasureState D μ p sample)
        (∑l : Fin n,anisotropicProcessMagnetization D μ p sample l •EuclideanSpace.single l 1):=by
      rw [map_sum]
      simp only [map_smul,smul_eq_mul]
    _=_:=congrArg
      (fderiv ℝ (fun x=>anisotropicRestartMeanSquare D μ sample.1 p x r)
        (anisotropicMeasureState D μ p sample)) hv.symm

private theorem weighted_free_sum (s : RSBScheme k) (a : ℝ) (ha:0≤a) (has:a ≤ s.m 1)
    (hq:s.q 1=0) (Mv : Fin n→ℝ) (F : Fin n→Paper.Overlap→ℝ) :
    (∑l : Fin n,Mv l*(∫r,F l r ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a))/(n:ℝ)=
      ∫r,(∑l : Fin n,Mv l*F l r)/(n:ℝ) ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a:=by
  simp_rw [←integral_const_mul]
  rw [←integral_cavityFiniteFree_finset_sum Finset.univ s a ha has hq,integral_div]

 theorem cavityFiniteRestObservableGroupedValue_at_native
    (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (ha : 0≤a)
    (has : a ≤ s.m 1) (hq : s.q 1=0) (J : ℕ) (hJ : J≤k+2)
    (z : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 nativeRest_zero_mem
    let μ:=Paper.parisiSchemeMeasure s
    let q:=anisotropicSchemeNode s (k+2-J) (by omega)
    let P:=anisotropicProcessParameter D μ q z.1
    cavityFiniteRestObservableGroupedValue s n β ρ hβ hρ J P
      (cavityOuterStieltjesWeight (anisotropicSchemeMass s) a (k+1))
      (cavityNativeResponseChargeDepth k) (cavityNativeResponseChargeParameter D s z.1) z.2
      (cavityNativeResponseLastCentered D s a J P)=
      cavityZeroRestResponseIntegrand μ n β ρ hβ hρ a q z:=by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 nativeRest_zero_mem
  let Rest:=followupCavityRestSpinModel n β ρ hβ hρ
  let B:=followupCavityScalarBeta n β ρ
  let μ:=Paper.parisiSchemeMeasure s
  let q:=anisotropicSchemeNode s (k+2-J) (by omega)
  let P:=anisotropicProcessParameter D μ q z.1
  let xr:=(cavityZeroMarkedSampleSplit n z).1
  let xs:=(cavityZeroMarkedSampleSplit n z).2
  let Mv:=fun i : Fin n=>anisotropicProcessMagnetization Rest μ q xr.1 i
  let H:Fin n→Fin n→ℝ:=fun l i=>nativeAnisotropicProcessHessianMatrix Rest μ q xr.1 l i
  let m:=M B μ q xs.1
  let c:=C B μ q xs.1
  let f:=scalarCenteredSquare B μ q xs.1
  let E:=fun (i l : Fin n)=>fderiv ℝ (fun Q=>anisotropicFinitePairSecond D s J Q
    (anisotropicOrderedCoupling i.castSucc (Fin.last n))) P
      (anisotropicCoordinateDirection (n+1) l.castSucc)
  let G:=fun (l : Fin n) (r : Paper.Overlap)=>if q<r then
    scalarFutureSquareExtended B μ q r (parisiPhysicalSplitState B 0 μ q xs.1)*
      fderiv ℝ (fun x=>anisotropicRestartMeanSquare Rest μ xr.1.1 q x r)
        (anisotropicMeasureState Rest μ q xr.1) (EuclideanSpace.single l 1) else 0
  have hf:cavityNativeResponseLastCentered D s a J P=f:=
    cavityFixedRowNativeLastCentered_zero s n β ρ hβ hρ a J hJ z.1
  have hm:parisiFDeriv s B J (P (Sum.inr (Fin.last n)))=m:=
    cavityFiniteScalarMean_at_native_scheme_node s n β ρ hβ hρ J hJ z.1
  have hc:parisiFSecond s B J (P (Sum.inr (Fin.last n)))=c:=
    cavityFiniteScalarHessian_at_native_scheme_node s n β ρ hβ hρ J hJ z.1
  have hM (i : Fin n):anisotropicFiniteFeatureMean Rest s J (fun σ=>Paper.spinSign (σ i))
      (cavityRestParameterProjection n P)=Mv i:=
    cavityFiniteRestMean_at_zero_native_scheme_node s n β ρ hβ hρ J hJ i z.1
  have hH (l i : Fin n):fderiv ℝ (anisotropicFiniteFeatureMean Rest s J
      (fun σ=>Paper.spinSign (σ i))) (cavityRestParameterProjection n P)
        (anisotropicCoordinateDirection n l)=H l i:=by
    rw [cavityRestProcessParameter_zero]
    exact cavityFiniteRestHessian_at_native_scheme_node Rest s J hJ i l xr.1
  have hE (l : Fin n):(∑i : Fin n,E i l)/(n:ℝ)=
      -2*Paper.parisiCDF μ q*m^2*(∑i : Fin n,Mv i*H l i)/(n:ℝ)-
      ∫r,G l r ∂parisiFreeMeasure μ a:=
    cavityFinitePairSecond_average_old_at_native_scheme_node s n β ρ hβ hρ J hJ a ha has hq z.1 l
  have hsumcurrent:(∑l : Fin n,Mv l*(∑i : Fin n,Mv i*H l i))/(n:ℝ)^2=
      cavityZeroRestMixedHessian Rest μ q q xr.1:=by
    rw [rest_mixed_hessian_sum]
    congr 1
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    ring
  have he:(∑l : Fin n,Mv l*(∑i : Fin n,E i l))/(n:ℝ)^2=
      -2*Paper.parisiCDF μ q*m^2*cavityZeroRestMixedHessian Rest μ q q xr.1-
      ∫r,if q<r then scalarFutureSquareExtended B μ q r
        (parisiPhysicalSplitState B 0 μ q xs.1)*cavityZeroRestFutureFieldDerivative Rest μ q r xr.1
        else 0 ∂parisiFreeMeasure μ a:=by
    have hn:(∑l : Fin n,Mv l*(∑i : Fin n,E i l))/(n:ℝ)^2=
        (∑l : Fin n,Mv l*((∑i : Fin n,E i l)/(n:ℝ)))/(n:ℝ):=by
      have hsum:(∑l : Fin n,Mv l*((∑i : Fin n,E i l)/(n:ℝ)))=
          (∑l : Fin n,Mv l*(∑i : Fin n,E i l))/(n:ℝ):=by
        calc
          _=∑l : Fin n,(Mv l*(∑i : Fin n,E i l))/(n:ℝ):=
            Finset.sum_congr rfl fun l _=>by ring
          _=_:=by rw [Finset.sum_div]
      rw [hsum]
      ring
    rw [hn]
    simp_rw [hE,mul_sub]
    rw [Finset.sum_sub_distrib,sub_div,weighted_free_sum s a ha has hq]
    have hcur:(∑l : Fin n,Mv l*(-2*Paper.parisiCDF μ q*m^2*(∑i : Fin n,Mv i*H l i)/(n:ℝ)))/(n:ℝ)=
        -2*Paper.parisiCDF μ q*m^2*cavityZeroRestMixedHessian Rest μ q q xr.1:=by
      have hsum:(∑l : Fin n,Mv l*(-2*Paper.parisiCDF μ q*m^2*(∑i : Fin n,Mv i*H l i)/(n:ℝ)))=
          ((-2*Paper.parisiCDF μ q*m^2)/(n:ℝ))*(∑l : Fin n,Mv l*(∑i : Fin n,Mv i*H l i)):=by
        conv_rhs => rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _=>by ring
      rw [hsum,←hsumcurrent]
      ring
    rw [hcur]
    congr 1
    apply integral_congr_ae
    exact .of_forall fun r=>by
      dsimp only [G]
      by_cases hr:q<r
      · simp only [if_pos hr]
        rw [show (∑l : Fin n,Mv l*(scalarFutureSquareExtended B μ q r
            (parisiPhysicalSplitState B 0 μ q xs.1)*
            fderiv ℝ (fun x=>anisotropicRestartMeanSquare Rest μ xr.1.1 q x r)
              (anisotropicMeasureState Rest μ q xr.1) (EuclideanSpace.single l 1)))=
            scalarFutureSquareExtended B μ q r (parisiPhysicalSplitState B 0 μ q xs.1)*
              (∑l : Fin n,Mv l*fderiv ℝ (fun x=>anisotropicRestartMeanSquare Rest μ xr.1.1 q x r)
                (anisotropicMeasureState Rest μ q xr.1) (EuclideanSpace.single l 1)) from by
              rw [Finset.mul_sum];exact Finset.sum_congr rfl fun l _=>by ring]
        rw [weighted_basis_apply Rest μ q r xr.1]
        unfold cavityZeroRestFutureFieldDerivative
        ring
      · simp only [if_neg hr,mul_zero,Finset.sum_const_zero,zero_div]
  have hcharges:
      (∑r : Option (Option (Fin (k+1))),cavityOuterStieltjesWeight (anisotropicSchemeMass s) a (k+1) r*
        parisiFDeriv s B (cavityNativeResponseChargeDepth k r)
          (cavityNativeResponseChargeParameter D s z.1 r (Sum.inr (Fin.last n)))*
        (∑i : Fin n,anisotropicFiniteFeatureMean Rest s (cavityNativeResponseChargeDepth k r)
          (fun σ=>Paper.spinSign (σ i))
          (cavityRestParameterProjection n (cavityNativeResponseChargeParameter D s z.1 r))*
            (∑l : Fin n,Mv l*H l i)))/(n:ℝ)^2=
      ∫r,M B μ r xs.1*cavityZeroRestMixedHessian Rest μ r q xr.1 ∂parisiFreeMeasure μ a:=by
    have hsc (r : Option (Option (Fin (k+1)))):
        parisiFDeriv s B (cavityNativeResponseChargeDepth k r)
          (cavityNativeResponseChargeParameter D s z.1 r (Sum.inr (Fin.last n)))=
          M B μ (cavityOuterSchemeChargeNode s r) xs.1:=
      cavityFiniteScalarMean_at_native_scheme_charge s n β ρ hβ hρ r z.1
    have hrc (r : Option (Option (Fin (k+1)))) (i : Fin n):
        anisotropicFiniteFeatureMean Rest s (cavityNativeResponseChargeDepth k r)
          (fun σ=>Paper.spinSign (σ i))
          (cavityRestParameterProjection n (cavityNativeResponseChargeParameter D s z.1 r))=
          anisotropicProcessMagnetization Rest μ (cavityOuterSchemeChargeNode s r) xr.1 i:=
      cavityFiniteRestMean_at_zero_native_scheme_charge s n β ρ hβ hρ r i z.1
    calc
      _=(∑r : Option (Option (Fin (k+1))),cavityOuterStieltjesWeight (anisotropicSchemeMass s) a (k+1) r*
          M B μ (cavityOuterSchemeChargeNode s r) xs.1*
          (∑i : Fin n,anisotropicProcessMagnetization Rest μ (cavityOuterSchemeChargeNode s r) xr.1 i*
            (∑l : Fin n,Mv l*H l i)))/(n:ℝ)^2:=by
        congr 1
        apply Finset.sum_congr rfl
        intro r _
        have hi:(∑i : Fin n,anisotropicFiniteFeatureMean Rest s (cavityNativeResponseChargeDepth k r)
            (fun σ=>Paper.spinSign (σ i))
            (cavityRestParameterProjection n (cavityNativeResponseChargeParameter D s z.1 r))*
            (∑l : Fin n,Mv l*H l i))=
            ∑i : Fin n,anisotropicProcessMagnetization Rest μ (cavityOuterSchemeChargeNode s r) xr.1 i*
              (∑l : Fin n,Mv l*H l i):=by
          apply Finset.sum_congr rfl
          intro i _
          rw [hrc r i]
        rw [hsc r,hi]
      _=_:=by
        rw [←cavityOuterSchemeCharge_sum_eq_actual_free s a ha has hq,Finset.sum_div]
        apply Finset.sum_congr rfl
        intro r _
        rw [rest_mixed_hessian_sum]
        ring
  unfold cavityFiniteRestObservableGroupedValue
  dsimp only
  rw [hf,hm,hc]
  dsimp only [D,Rest,P,μ,q] at hM hH
  simp only [hM,hH]
  simp only [mul_div_assoc]
  rw [he,hcharges,←rest_trace_hessian_sum,←rest_mixed_hessian_sum]
  change f*m^2*cavityZeroRestHessianSquare Rest μ q xr.1+
    f*(-2*Paper.parisiCDF μ q*m^2*cavityZeroRestMixedHessian Rest μ q q xr.1-
      ∫r,if q<r then scalarFutureSquareExtended B μ q r
        (parisiPhysicalSplitState B 0 μ q xs.1)*cavityZeroRestFutureFieldDerivative Rest μ q r xr.1 else 0
        ∂parisiFreeMeasure μ a)+4*m^2*c*cavityZeroRestMixedHessian Rest μ q q xr.1+
    2*f*m*Paper.spinSign xs.2*cavityZeroRestTerminalHessian Rest μ q xr-
    2*f*m*(∫r,M B μ r xs.1*cavityZeroRestMixedHessian Rest μ r q xr.1 ∂parisiFreeMeasure μ a)=_
  have hs1:scalarResponseSample 1 B μ q 0 0 xs=m^2*c:=rfl
  have hs5:scalarResponseSample 5 B μ q q 0 xs=f*m^2:=rfl
  have hs6 (r : Paper.Overlap):scalarResponseSample 6 B μ q q r xs=f*m*M B μ r xs.1:=rfl
  unfold cavityZeroRestResponseIntegrand
  dsimp only
  change _=cavityZeroRestHessianSquare Rest μ q xr.1*(f*m^2)+
    4*(cavityZeroRestMixedHessian Rest μ q q xr.1*(m^2*c))-
    2*Paper.parisiCDF μ q*(cavityZeroRestMixedHessian Rest μ q q xr.1*(f*m^2))+
    2*(cavityZeroRestTerminalHessian Rest μ q xr*(f*m*Paper.spinSign xs.2))-
    (∫r,if q<r then cavityZeroRestFutureFieldDerivative Rest μ q r xr.1*
      (f*scalarFutureSquareExtended B μ q r (parisiPhysicalSplitState B 0 μ q xs.1))
      else 0 ∂parisiFreeMeasure μ a)-
    2*(∫r,cavityZeroRestMixedHessian Rest μ r q xr.1*(f*m*M B μ r xs.1)
      ∂parisiFreeMeasure μ a)
  have hfuture:f*(∫r,if q<r then scalarFutureSquareExtended B μ q r
      (parisiPhysicalSplitState B 0 μ q xs.1)*cavityZeroRestFutureFieldDerivative Rest μ q r xr.1 else 0
      ∂parisiFreeMeasure μ a)=∫r,if q<r then cavityZeroRestFutureFieldDerivative Rest μ q r xr.1*
        (f*scalarFutureSquareExtended B μ q r (parisiPhysicalSplitState B 0 μ q xs.1)) else 0
        ∂parisiFreeMeasure μ a:=by
    rw [←integral_const_mul]
    apply integral_congr_ae
    exact .of_forall fun r=>by
      dsimp only
      by_cases hr:q<r
      · simp only [if_pos hr]
        ring
      · simp only [if_neg hr,mul_zero]
  have hlast:f*m*(∫r,M B μ r xs.1*cavityZeroRestMixedHessian Rest μ r q xr.1 ∂parisiFreeMeasure μ a)=
      ∫r,cavityZeroRestMixedHessian Rest μ r q xr.1*(f*m*M B μ r xs.1) ∂parisiFreeMeasure μ a:=by
    rw [←integral_const_mul]
    apply integral_congr_ae
    exact .of_forall fun r=>by ring
  rw [mul_sub,hfuture]
  have hlast2:2*f*m*(∫r,M B μ r xs.1*cavityZeroRestMixedHessian Rest μ r q xr.1 ∂parisiFreeMeasure μ a)=
      2*(∫r,cavityZeroRestMixedHessian Rest μ r q xr.1*(f*m*M B μ r xs.1) ∂parisiFreeMeasure μ a):=by
    rw [←hlast];ring
  rw [hlast2]
  ring

end QuantitativeFollowup
