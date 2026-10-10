module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteFiveGrouping
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeResponseDefinitions
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeChargeMeans
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteFreeFutureProduct
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteFreeLinearity
public import QuantitativeFollowup.FollowupCavityCppZeroResponseDensityEvaluation

@[expose] public section

/-! The actual signed-charge density group is the genuine native density
integrand. Every root, current and strict-future charge is retained. -/
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
 theorem nativeDensity_zero_mem : (0:ℝ)∈Icc 0 1:=⟨le_rfl,zero_le_one⟩

private theorem average_free_integral {I : Type*} [Fintype I]
    (s : RSBScheme k) (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (F : I→Paper.Overlap→ℝ) (C : ℝ) :
    (∑i : I,∫r,F i r ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)/C=
      ∫r,(∑i : I,F i r)/C ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a:=by
  rw [←integral_cavityFiniteFree_finset_sum Finset.univ s a ha has hq,integral_div]

private theorem double_charge_integral
    (s : RSBScheme k) (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (F : Paper.Overlap→Paper.Overlap→ℝ) :
    (∑c : Option (Option (Fin (k+1))),∑d : Option (Option (Fin (k+1))),
      cavityOuterStieltjesWeight (anisotropicSchemeMass s) a (k+1) c*
      cavityOuterStieltjesWeight (anisotropicSchemeMass s) a (k+1) d*
      F (cavityOuterSchemeChargeNode s c) (cavityOuterSchemeChargeNode s d))=
      ∫r,∫l,F r l ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a:=by
  have hi (c : Option (Option (Fin (k+1)))):
      (∑d : Option (Option (Fin (k+1))),
        cavityOuterStieltjesWeight (anisotropicSchemeMass s) a (k+1) c*
        cavityOuterStieltjesWeight (anisotropicSchemeMass s) a (k+1) d*
        F (cavityOuterSchemeChargeNode s c) (cavityOuterSchemeChargeNode s d))=
      cavityOuterStieltjesWeight (anisotropicSchemeMass s) a (k+1) c*
        (∫l,F (cavityOuterSchemeChargeNode s c) l
          ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a):=by
    simp only [mul_assoc]
    rw [←Finset.mul_sum,cavityOuterSchemeCharge_sum_eq_actual_free s a ha has hq]
  simp_rw [hi]
  exact cavityOuterSchemeCharge_sum_eq_actual_free s a ha has hq
    (fun r=>∫l,F r l ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)

 theorem cavityFiniteIncidentFreeDensityGroupedValue_at_native
    (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (ha : 0≤a)
    (has : a ≤ s.m 1) (hq : s.q 1=0) (J : ℕ) (hJ : J≤k+2)
    (z : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 nativeDensity_zero_mem
    let μ:=Paper.parisiSchemeMeasure s
    let q:=anisotropicSchemeNode s (k+2-J) (by omega)
    let P:=anisotropicProcessParameter D μ q z.1
    cavityFiniteIncidentFreeDensityGroupedValue s n β ρ hβ hρ a
      (cavityOuterStieltjesWeight (anisotropicSchemeMass s) a (k+1))
      (cavityNativeResponseChargeDepth k) (cavityNativeResponseChargeParameter D s z.1) z.2
      (cavityNativeResponseLastCentered D s a J P) (cavityNativeResponseRestCentered D s a J P)=
      cavityZeroDensityResponseIntegrand μ n β ρ hβ hρ a q z:=by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 nativeDensity_zero_mem
  let Rest:=followupCavityRestSpinModel n β ρ hβ hρ
  let B:=followupCavityScalarBeta n β ρ
  let μ:=Paper.parisiSchemeMeasure s
  let q:=anisotropicSchemeNode s (k+2-J) (by omega)
  let P:=anisotropicProcessParameter D μ q z.1
  let xr:=(cavityZeroMarkedSampleSplit n z).1
  let xs:=(cavityZeroMarkedSampleSplit n z).2
  let A:=cavitySignedResponseCenteredSelfOverlap Rest μ a q xr.1
  let f:=scalarCenteredSquare B μ q xs.1
  let w:=cavityOuterStieltjesWeight (anisotropicSchemeMass s) a (k+1)
  let jr:=cavityNativeResponseChargeDepth k
  let Pr:=cavityNativeResponseChargeParameter D s z.1
  let rnode:=cavityOuterSchemeChargeNode s
  let mr:=fun r=>M B μ r xs.1
  let M:=fun r i=>anisotropicProcessSpinResponse Rest μ r i xr.1
  have hA:cavityNativeResponseRestCentered D s a J P=A:=
    cavityFixedRowNativeRestCentered_zero s n β ρ hβ hρ a J hJ z.1
  have hf:cavityNativeResponseLastCentered D s a J P=f:=
    cavityFixedRowNativeLastCentered_zero s n β ρ hβ hρ a J hJ z.1
  have hm (c : Option (Option (Fin (k+1)))):
      parisiFDeriv s B (jr c) (Pr c (Sum.inr (Fin.last n)))=mr (rnode c):=
    cavityFiniteScalarMean_at_native_scheme_charge s n β ρ hβ hρ c z.1
  have hM (c : Option (Option (Fin (k+1)))) (i : Fin n):
      anisotropicFiniteFeatureMean Rest s (jr c) (fun σ=>Paper.spinSign (σ i))
        (cavityRestParameterProjection n (Pr c))=M (rnode c) i:=
    cavityFiniteRestMean_at_zero_native_scheme_charge s n β ρ hβ hρ c i z.1
  have hnode (c : Option (Option (Fin (k+1)))):
      scalarSchemeTransportNode s (k+2-jr c)=rnode c:=by
    apply Subtype.ext
    dsimp only [rnode,jr,cavityNativeResponseChargeDepth]
    rw [scalarSchemeTransportNode_coe s _ (by omega),
      cavityOuterSchemeChargeNode_eq_position]
    change s.q (k+2-(k+2-cavityOuterChargePosition (k+1) c))=s.q (cavityOuterChargePosition (k+1) c)
    congr 1
    have hc:=cavityOuterSchemeChargePosition_le c
    omega
  have hfuture (c : Option (Option (Fin (k+1)))):
      (n:ℝ)⁻¹*(∑i : Fin n,cavityFiniteIncidentFreeDensityFuture s n β ρ hβ hρ a (jr c) i (Pr c))=
        ∫l,if rnode c<l then cavityRestFutureSquare Rest μ (rnode c) l xr.1*
          scalarFutureSquareExtended B μ (rnode c) l
            (parisiPhysicalSplitState B 0 μ (rnode c) xs.1) else 0 ∂parisiFreeMeasure μ a:=by
    change (n:ℝ)⁻¹*(∑i : Fin n,∫l,
      if scalarSchemeTransportNode s (k+2-jr c)<l then cavityFiniteFutureSquare D s (jr c)
        (anisotropicEnergyMap D (Pr c))
        (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))) l else 0
      ∂parisiFreeMeasure μ a)=_
    rw [hnode]
    rw [mul_comm ((n:ℝ)⁻¹),←div_eq_mul_inv]
    rw [average_free_integral s a ha has hq]
    have hsum (l : Paper.Overlap):
        (∑i : Fin n,if rnode c<l then cavityFiniteFutureSquare D s (jr c)
          (anisotropicEnergyMap D (Pr c))
          (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))) l else 0)/(n:ℝ)=
        if rnode c<l then (∑i : Fin n,cavityFiniteFutureSquare D s (jr c)
          (anisotropicEnergyMap D (Pr c))
          (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))) l)/(n:ℝ) else 0:=by
      by_cases h:rnode c<l
      · simp only [if_pos h]
      · simp only [if_neg h,Finset.sum_const_zero,zero_div]
    trans ∫l,if rnode c<l then (∑i : Fin n,cavityFiniteFutureSquare D s (jr c)
      (anisotropicEnergyMap D (Pr c))
      (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))) l)/(n:ℝ)
      else 0 ∂parisiFreeMeasure μ a
    · exact integral_congr_ae (.of_forall hsum)
    have he:=cavityFiniteFreeFutureSquare_average_eq_native_product s n β ρ hβ hρ a ha has hq
      (jr c) (by dsimp only [jr,cavityNativeResponseChargeDepth];omega) z.1
    dsimp only [jr,cavityNativeResponseChargeDepth] at he
    rw [cavityFiniteResponseCharge_node s c] at he
    exact he
  unfold cavityFiniteIncidentFreeDensityGroupedValue
  dsimp only
  rw [hf,hA]
  change f*A/2*(1-∑c,w c)-
    f*A*(∑c,w c*Paper.spinSign xs.2*parisiFDeriv s B (jr c) (Pr c (Sum.inr (Fin.last n)))*
      ((n:ℝ)⁻¹*∑i,Paper.spinSign (z.2 i.castSucc)*
        anisotropicFiniteFeatureMean Rest s (jr c) (fun τ=>Paper.spinSign (τ i))
          (cavityRestParameterProjection n (Pr c))))+
    f*A/2*(∑c,∑d,w c*w d*parisiFDeriv s B (jr c) (Pr c (Sum.inr (Fin.last n)))*
      parisiFDeriv s B (jr d) (Pr d (Sum.inr (Fin.last n)))*((n:ℝ)⁻¹*∑i,
        anisotropicFiniteFeatureMean Rest s (jr c) (fun τ=>Paper.spinSign (τ i))
          (cavityRestParameterProjection n (Pr c))*
        anisotropicFiniteFeatureMean Rest s (jr d) (fun τ=>Paper.spinSign (τ i))
          (cavityRestParameterProjection n (Pr d))))+
    f*A/2*(∑c,w c*Paper.parisiCDF μ (scalarSchemeTransportNode s (k+2-jr c))*
      (parisiFDeriv s B (jr c) (Pr c (Sum.inr (Fin.last n))))^2*((n:ℝ)⁻¹*∑i,
        (anisotropicFiniteFeatureMean Rest s (jr c) (fun τ=>Paper.spinSign (τ i))
          (cavityRestParameterProjection n (Pr c)))^2))+
    f*A/2*(∑c,w c*((n:ℝ)⁻¹*∑i,
      cavityFiniteIncidentFreeDensityFuture s n β ρ hβ hρ a (jr c) i (Pr c)))=_
  simp only [hm,hM,hnode,hfuture]
  have ht (r : Paper.Overlap):
      (n:ℝ)⁻¹*(∑i : Fin n,Paper.spinSign (z.2 i.castSucc)*M r i)=
        cavityRestTerminalMeanPairing Rest μ r xr:=by
    simp only [cavityRestTerminalMeanPairing,div_eq_mul_inv,mul_comm]
    rfl
  have htwo (r l : Paper.Overlap):
      (n:ℝ)⁻¹*(∑i : Fin n,M r i*M l i)=cavityRestTwoTimeMeanPairing Rest μ r l xr.1:=by
    simp only [cavityRestTwoTimeMeanPairing,div_eq_mul_inv,mul_comm]
    rfl
  have hself (r : Paper.Overlap):
      (n:ℝ)⁻¹*(∑i : Fin n,(M r i)^2)=cavitySignedResponseSelfOverlap Rest μ r xr.1:=by
    simp only [cavitySignedResponseSelfOverlap,anisotropicSelectedMeanSquare,
      Finset.card_univ,Fintype.card_fin,div_eq_mul_inv,mul_comm]
    rfl
  simp_rw [ht,htwo,hself]
  have hzero:(∑c : Option (Option (Fin (k+1))),w c)=
      ∫r,(1:ℝ) ∂parisiFreeMeasure μ a:=by
    simpa only [mul_one] using cavityOuterSchemeCharge_sum_eq_actual_free s a ha has hq (fun _=>1)
  have h1:(∑c : Option (Option (Fin (k+1))),w c*Paper.spinSign xs.2*mr (rnode c)*
      cavityRestTerminalMeanPairing Rest μ (rnode c) xr)=
      ∫r,Paper.spinSign xs.2*mr r*cavityRestTerminalMeanPairing Rest μ r xr ∂parisiFreeMeasure μ a:=by
    simp only [mul_assoc]
    exact cavityOuterSchemeCharge_sum_eq_actual_free s a ha has hq
      (fun r=>Paper.spinSign xs.2*(mr r*cavityRestTerminalMeanPairing Rest μ r xr))
  have h2:(∑c : Option (Option (Fin (k+1))),∑d : Option (Option (Fin (k+1))),
      w c*w d*mr (rnode c)*mr (rnode d)*cavityRestTwoTimeMeanPairing Rest μ (rnode c) (rnode d) xr.1)=
      ∫r,∫l,mr r*mr l*cavityRestTwoTimeMeanPairing Rest μ r l xr.1
        ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a:=by
    simpa only [mul_assoc] using double_charge_integral s a ha has hq
      (fun r l=>mr r*mr l*cavityRestTwoTimeMeanPairing Rest μ r l xr.1)
  have h3:(∑c : Option (Option (Fin (k+1))),w c*Paper.parisiCDF μ (rnode c)*
      mr (rnode c)^2*cavitySignedResponseSelfOverlap Rest μ (rnode c) xr.1)=
      ∫r,Paper.parisiCDF μ r*mr r^2*cavitySignedResponseSelfOverlap Rest μ r xr.1
        ∂parisiFreeMeasure μ a:=by
    simp only [mul_assoc]
    exact cavityOuterSchemeCharge_sum_eq_actual_free s a ha has hq
      (fun r=>Paper.parisiCDF μ r*(mr r^2*cavitySignedResponseSelfOverlap Rest μ r xr.1))
  have h4:(∑c : Option (Option (Fin (k+1))),w c*(∫l,if rnode c<l then
      cavityRestFutureSquare Rest μ (rnode c) l xr.1*scalarFutureSquareExtended B μ (rnode c) l
        (parisiPhysicalSplitState B 0 μ (rnode c) xs.1) else 0 ∂parisiFreeMeasure μ a))=
      ∫r,∫l,if r<l then cavityRestFutureSquare Rest μ r l xr.1*scalarFutureSquareExtended B μ r l
        (parisiPhysicalSplitState B 0 μ r xs.1) else 0
        ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a:=
    cavityOuterSchemeCharge_sum_eq_actual_free s a ha has hq
      (fun r=>∫l,if r<l then cavityRestFutureSquare Rest μ r l xr.1*
        scalarFutureSquareExtended B μ r l (parisiPhysicalSplitState B 0 μ r xs.1)
        else 0 ∂parisiFreeMeasure μ a)
  rw [hzero,h1,h2,h3,h4]
  have hfactor (F : Paper.Overlap→ℝ):f*A*(∫r,F r ∂parisiFreeMeasure μ a)=
      ∫r,A*f*F r ∂parisiFreeMeasure μ a:=by
    rw [←integral_const_mul]
    apply integral_congr_ae
    exact .of_forall fun r=>by ring
  have hdouble (F : Paper.Overlap→Paper.Overlap→ℝ):
      f*A*(∫r,∫l,F r l ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a)=
      ∫r,∫l,A*f*F r l ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a:=by
    rw [←integral_const_mul]
    apply integral_congr_ae
    exact .of_forall fun r=>by
      dsimp only
      rw [←integral_const_mul]
      apply integral_congr_ae
      exact .of_forall fun l=>by ring
  unfold cavityZeroDensityResponseIntegrand
  dsimp only
  change _=((1-(∫r,(1:ℝ) ∂parisiFreeMeasure μ a))/2)*(A*f)-
    (∫r,cavityRestTerminalMeanPairing Rest μ r xr*A*(f*Paper.spinSign xs.2*mr r)
      ∂parisiFreeMeasure μ a)+
    (1/2:ℝ)*(∫r,∫l,cavityRestTwoTimeMeanPairing Rest μ r l xr.1*A*(f*mr r*mr l)
      ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a)+
    (1/2:ℝ)*(∫r,Paper.parisiCDF μ r*(cavitySignedResponseSelfOverlap Rest μ r xr.1*A*(f*(mr r)^2))
      ∂parisiFreeMeasure μ a)+
    (1/2:ℝ)*(∫r,∫l,if r<l then cavityRestFutureSquare Rest μ r l xr.1*A*
      (f*scalarFutureSquareExtended B μ r l (parisiPhysicalSplitState B 0 μ r xs.1)) else 0
      ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a)
  rw [show f*A/2*(1-∫r,(1:ℝ) ∂parisiFreeMeasure μ a)=
    ((1-∫r,(1:ℝ) ∂parisiFreeMeasure μ a)/2)*(A*f) from by ring]
  have hhalffactor (F : Paper.Overlap→ℝ):
      f*A/2*(∫r,F r ∂parisiFreeMeasure μ a)=
        (1/2:ℝ)*(∫r,A*f*F r ∂parisiFreeMeasure μ a):=by rw [←hfactor];ring
  have hhalfdouble (F : Paper.Overlap→Paper.Overlap→ℝ):
      f*A/2*(∫r,∫l,F r l ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a)=
        (1/2:ℝ)*(∫r,∫l,A*f*F r l ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a):=by
    rw [←hdouble];ring
  rw [hfactor,hhalfdouble,hhalffactor,hhalfdouble]
  have he₁ : (∫r,A*f*(Paper.spinSign xs.2*mr r*cavityRestTerminalMeanPairing Rest μ r xr)
      ∂parisiFreeMeasure μ a)=
      ∫r,cavityRestTerminalMeanPairing Rest μ r xr*A*(f*Paper.spinSign xs.2*mr r)
        ∂parisiFreeMeasure μ a :=by
    apply integral_congr_ae
    exact .of_forall fun r=>by dsimp only;ring
  have he₂ : (∫r,∫l,A*f*(mr r*mr l*cavityRestTwoTimeMeanPairing Rest μ r l xr.1)
      ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a)=
      ∫r,∫l,cavityRestTwoTimeMeanPairing Rest μ r l xr.1*A*(f*mr r*mr l)
        ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a :=by
    apply integral_congr_ae
    exact .of_forall fun r=>by
      dsimp only
      apply integral_congr_ae
      exact .of_forall fun l=>by dsimp only;ring
  have he₃ : (∫r,A*f*(Paper.parisiCDF μ r*mr r^2*cavitySignedResponseSelfOverlap Rest μ r xr.1)
      ∂parisiFreeMeasure μ a)=
      ∫r,Paper.parisiCDF μ r*(cavitySignedResponseSelfOverlap Rest μ r xr.1*A*(f*mr r^2))
        ∂parisiFreeMeasure μ a :=by
    apply integral_congr_ae
    exact .of_forall fun r=>by dsimp only;ring
  have he₄ : (∫r,∫l,A*f*(if r<l then cavityRestFutureSquare Rest μ r l xr.1*
      scalarFutureSquareExtended B μ r l (parisiPhysicalSplitState B 0 μ r xs.1) else 0)
      ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a)=
      ∫r,∫l,if r<l then cavityRestFutureSquare Rest μ r l xr.1*A*
        (f*scalarFutureSquareExtended B μ r l (parisiPhysicalSplitState B 0 μ r xs.1)) else 0
        ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a :=by
    apply integral_congr_ae
    exact .of_forall fun r=>by
      dsimp only
      apply integral_congr_ae
      exact .of_forall fun l=>by dsimp only;split_ifs <;> ring
  rw [he₁,he₂,he₃,he₄]

end QuantitativeFollowup
