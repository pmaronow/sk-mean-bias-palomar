module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteFiveGrouping
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeResponseDefinitions
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeChargeMeans
public import QuantitativeFollowup.FollowupCavityCppZeroResponseLastEvaluation

@[expose] public section

/-! The last-observable part of the actual finite posterior response is
the native last-response integrand, pointwise on the whole marked path.
The current CDF, actual future differential and terminal mark are retained. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper FRSB
open scoped BigOperators
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 theorem nativeLast_zero_mem : (0:ℝ)∈Icc 0 1:=⟨le_rfl,zero_le_one⟩

theorem cavityFiniteLastObservableGroupedValue_at_native
    (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (ha : 0≤a)
    (has : a ≤ s.m 1) (hq : s.q 1=0) (J : ℕ) (hJ : J≤k+2)
    (z : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 nativeLast_zero_mem
    let μ:=Paper.parisiSchemeMeasure s
    let q:=anisotropicSchemeNode s (k+2-J) (by omega)
    let P:=anisotropicProcessParameter D μ q z.1
    cavityFiniteLastObservableGroupedValue s n β ρ hβ hρ J P
      (cavityOuterStieltjesWeight (anisotropicSchemeMass s) a (k+1))
      (cavityNativeResponseChargeDepth k) (cavityNativeResponseChargeParameter D s z.1) z.2
      (cavityNativeResponseRestCentered D s a J P)=
      cavityZeroLastResponseIntegrand μ n β ρ hβ hρ a q z :=by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 nativeLast_zero_mem
  let Rest:=followupCavityRestSpinModel n β ρ hβ hρ
  let B:=followupCavityScalarBeta n β ρ
  let μ:=Paper.parisiSchemeMeasure s
  let q:=anisotropicSchemeNode s (k+2-J) (by omega)
  let P:=anisotropicProcessParameter D μ q z.1
  let xr:=(cavityZeroMarkedSampleSplit n z).1
  let xs:=(cavityZeroMarkedSampleSplit n z).2
  let A:=cavitySignedResponseCenteredSelfOverlap Rest μ a q xr.1
  let m:=M B μ q xs.1
  let c:=C B μ q xs.1
  let self:=cavitySignedResponseSelfOverlap Rest μ q xr.1
  let F:=fun r : Paper.Overlap=>if q<r then
    cavityRestFutureSquare Rest μ q r xr.1*scalarFutureSquareDerivativeExtended B μ q r
      (parisiPhysicalSplitState B 0 μ q xs.1) else 0
  let G:=fun r : Paper.Overlap=>M B μ r xs.1*cavityRestTwoTimeMeanPairing Rest μ q r xr.1
  have hcenter:cavityNativeResponseRestCentered D s a J P=A:=
    cavityFixedRowNativeRestCentered_zero s n β ρ hβ hρ a J hJ z.1
  have hm:parisiFDeriv s B J (P (Sum.inr (Fin.last n)))=m:=
    cavityFiniteScalarMean_at_native_scheme_node s n β ρ hβ hρ J hJ z.1
  have hc:parisiFSecond s B J (P (Sum.inr (Fin.last n)))=c:=
    cavityFiniteScalarHessian_at_native_scheme_node s n β ρ hβ hρ J hJ z.1
  have hself:(∑i : Fin n,(anisotropicFiniteFeatureMean Rest s J
      (fun σ=>Paper.spinSign (σ i)) (cavityRestParameterProjection n P))^2)/(n:ℝ)=self:=
    cavityFiniteRestSelf_at_zero_native_scheme_node s n β ρ hβ hρ J hJ z.1
  have he:(∑i : Fin n,fderiv ℝ (fun Q=>anisotropicFinitePairSecond D s J Q
      (anisotropicOrderedCoupling i.castSucc (Fin.last n))) P
      (anisotropicCoordinateDirection (n+1) (Fin.last n)))/(n:ℝ)=
      -2*Paper.parisiCDF μ q*m*c*self-∫r,F r ∂parisiFreeMeasure μ a:=
    cavityFinitePairSecond_average_last_at_native_scheme_node s n β ρ hβ hρ J hJ a ha has hq z.1
  have hM (i : Fin n):anisotropicFiniteFeatureMean Rest s J (fun σ=>Paper.spinSign (σ i))
      (cavityRestParameterProjection n P)=anisotropicProcessSpinResponse Rest μ q i xr.1:=
    cavityFiniteRestMean_at_zero_native_scheme_node s n β ρ hβ hρ J hJ i z.1
  have hterminal:(∑i : Fin n,Paper.spinSign (z.2 i.castSucc)*
      anisotropicFiniteFeatureMean Rest s J (fun σ=>Paper.spinSign (σ i))
        (cavityRestParameterProjection n P))/(n:ℝ)=cavityRestTerminalMeanPairing Rest μ q xr:=by
    simp_rw [hM]
    rfl
  have hchargem (r : Option (Option (Fin (k+1)))):
      parisiFDeriv s B (cavityNativeResponseChargeDepth k r)
        (cavityNativeResponseChargeParameter D s z.1 r (Sum.inr (Fin.last n)))=
      M B μ (cavityOuterSchemeChargeNode s r) xs.1:=
    cavityFiniteScalarMean_at_native_scheme_charge s n β ρ hβ hρ r z.1
  have hchargeM (r : Option (Option (Fin (k+1)))) (i : Fin n):
      anisotropicFiniteFeatureMean Rest s (cavityNativeResponseChargeDepth k r)
        (fun σ=>Paper.spinSign (σ i))
        (cavityRestParameterProjection n (cavityNativeResponseChargeParameter D s z.1 r))=
      anisotropicProcessSpinResponse Rest μ (cavityOuterSchemeChargeNode s r) i xr.1:=
    cavityFiniteRestMean_at_zero_native_scheme_charge s n β ρ hβ hρ r i z.1
  have hcharges:
      (∑r : Option (Option (Fin (k+1))),
        cavityOuterStieltjesWeight (anisotropicSchemeMass s) a (k+1) r*
        parisiFDeriv s B (cavityNativeResponseChargeDepth k r)
          (cavityNativeResponseChargeParameter D s z.1 r (Sum.inr (Fin.last n)))*
        (∑i : Fin n,anisotropicFiniteFeatureMean Rest s J (fun σ=>Paper.spinSign (σ i))
          (cavityRestParameterProjection n P)*
          anisotropicFiniteFeatureMean Rest s (cavityNativeResponseChargeDepth k r)
            (fun σ=>Paper.spinSign (σ i))
            (cavityRestParameterProjection n (cavityNativeResponseChargeParameter D s z.1 r))))/(n:ℝ)=
        ∫r,G r ∂parisiFreeMeasure μ a:=by
    rw [←cavityOuterSchemeCharge_sum_eq_actual_free s a ha has hq G,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro r _
    rw [hchargem r]
    have hinner:
        (∑i : Fin n,anisotropicFiniteFeatureMean Rest s J (fun σ=>Paper.spinSign (σ i))
          (cavityRestParameterProjection n P)*
          anisotropicFiniteFeatureMean Rest s (cavityNativeResponseChargeDepth k r)
            (fun σ=>Paper.spinSign (σ i))
            (cavityRestParameterProjection n (cavityNativeResponseChargeParameter D s z.1 r)))=
        ∑i : Fin n,anisotropicProcessSpinResponse Rest μ q i xr.1*
          anisotropicProcessSpinResponse Rest μ (cavityOuterSchemeChargeNode s r) i xr.1:=by
      exact Finset.sum_congr rfl fun i _=>congrArg₂ (fun x y : ℝ=>x*y) (hM i) (hchargeM r i)
    rw [hinner]
    dsimp only [G,cavityRestTwoTimeMeanPairing]
    ring
  have hfuture:A*m*(∫r,F r ∂parisiFreeMeasure μ a)=
      ∫r,if q<r then cavityRestFutureSquare Rest μ q r xr.1*A*
        scalarResponseSample 2 B μ q r 0 xs else 0 ∂parisiFreeMeasure μ a:=by
    rw [←integral_const_mul]
    apply integral_congr_ae
    exact .of_forall fun r=>by
      dsimp only [F]
      split_ifs
      · have hs2:scalarResponseSample 2 B μ q r 0 xs=
            m*scalarFutureSquareDerivativeExtended B μ q r
              (parisiPhysicalSplitState B 0 μ q xs.1):=rfl
        rw [hs2]
        ring
      · ring
  have hpast:A*m*c*(∫r,G r ∂parisiFreeMeasure μ a)=
      ∫r,cavityRestTwoTimeMeanPairing Rest μ q r xr.1*A*
        scalarResponseSample 3 B μ q r 0 xs ∂parisiFreeMeasure μ a:=by
    rw [←integral_const_mul]
    apply integral_congr_ae
    exact .of_forall fun r=>by
      dsimp only [G]
      have hs3:scalarResponseSample 3 B μ q r 0 xs=m*c*M B μ r xs.1:=rfl
      rw [hs3]
      ring
  unfold cavityFiniteLastObservableGroupedValue
  dsimp only
  rw [hcenter,hm,hc]
  simp only [mul_div_assoc]
  rw [hself,he,hterminal,hcharges]
  change A*(c^2*self+m*(-2*Paper.parisiCDF μ q*m*c*self-∫r,F r ∂parisiFreeMeasure μ a)+
    2*m*c*Paper.spinSign xs.2*cavityRestTerminalMeanPairing Rest μ q xr-
    2*m*c*(∫r,G r ∂parisiFreeMeasure μ a))=cavityZeroLastResponseIntegrand μ n β ρ hβ hρ a q z
  have halgebra:
      A*(c^2*self+m*(-2*Paper.parisiCDF μ q*m*c*self-∫r,F r ∂parisiFreeMeasure μ a)+
        2*m*c*Paper.spinSign xs.2*cavityRestTerminalMeanPairing Rest μ q xr-
        2*m*c*(∫r,G r ∂parisiFreeMeasure μ a))=
      self*A*c^2-2*Paper.parisiCDF μ q*(self*A*m^2*c)-A*m*(∫r,F r ∂parisiFreeMeasure μ a)+
        2*(cavityRestTerminalMeanPairing Rest μ q xr*A)*(m*c*Paper.spinSign xs.2)-
        2*(A*m*c*(∫r,G r ∂parisiFreeMeasure μ a)):=by ring
  rw [halgebra,hfuture,hpast]
  change _=self*A*scalarResponseSample 0 B μ q q 0 xs-
    2*Paper.parisiCDF μ q*(self*A*scalarResponseSample 1 B μ q q 0 xs)-
    (∫r,if q<r then cavityRestFutureSquare Rest μ q r xr.1*A*
      scalarResponseSample 2 B μ q r 0 xs else 0 ∂parisiFreeMeasure μ a)+
    2*((cavityRestTerminalMeanPairing Rest μ q xr*A)*(m*c*Paper.spinSign xs.2))-
    2*(∫r,cavityRestTwoTimeMeanPairing Rest μ q r xr.1*A*
      scalarResponseSample 3 B μ q r 0 xs ∂parisiFreeMeasure μ a)
  have hs0:scalarResponseSample 0 B μ q q 0 xs=c^2:=rfl
  have hs1:scalarResponseSample 1 B μ q q 0 xs=m^2*c:=rfl
  rw [hs0,hs1]
  ring

end QuantitativeFollowup
