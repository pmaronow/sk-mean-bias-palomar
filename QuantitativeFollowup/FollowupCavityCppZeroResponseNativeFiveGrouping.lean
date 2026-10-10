module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeResponseDefinitions
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeResponseIntegral
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteFiveGrouping

@[expose] public section

/-! The actual native five-term integrand, grouped before taking any
expectation. Every signed outer charge is evaluated at its genuine original
node. The right-CDF and strict-future terms are retained unchanged. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 theorem nativeFive_zero_mem : (0:ℝ)∈Icc 0 1 := ⟨le_rfl,zero_le_one⟩

private theorem native_response_integrand_eq_charge_five
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0) (d : ℕ) (hd : d≤k+2)
    (i : Fin n) (z : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)) :
    let P:=anisotropicProcessParameter D (Paper.parisiSchemeMeasure s)
      (anisotropicSchemeNode s (k+2-d) (by omega)) z.1
    let Q:=anisotropicEnergyMap D P
    let K:=anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))
    let f:=cavityFixedRowLastFieldSquare D s d
    let g:=cavityFixedRowRestFieldSquare D s d
    let Fbar:=cavityNativeResponseLastCentered D s a d P
    let Abar:=cavityNativeResponseRestCentered D s a d P
    let w:=cavityOuterStieltjesWeight (anisotropicSchemeMass s) a (k+1)
    let Pr:=cavityNativeResponseChargeParameter D s z.1
    let Score:=Paper.spinSign (z.2 i.castSucc)*Paper.spinSign (z.2 (Fin.last n))-
      ∑r,w r*anisotropicFiniteFeatureMean D s (cavityNativeResponseChargeDepth k r) K (Pr r)
    cavityFixedRowNativeFiniteResponseIntegrand D s a d hd i z=
      exponentialDensityHessian f Q K K*Abar+
      Fbar*exponentialDensityHessian g Q K K+
      2*fderiv ℝ f Q K*fderiv ℝ g Q K+
      2*Score*(fderiv ℝ f Q K*Abar+Fbar*fderiv ℝ g Q K)+
      Fbar*Abar*(Score^2-∑r,w r*anisotropicFinitePairSecond D s
        (cavityNativeResponseChargeDepth k r) (Pr r)
        (anisotropicOrderedCoupling i.castSucc (Fin.last n))) :=by
  dsimp only
  unfold cavityFixedRowNativeFiniteResponseIntegrand
  rw [integral_cavityNativeChargeFeature_eq_finite_sum D s a ha has hq,
    integral_cavityNativeChargeSecond_eq_finite_sum D s a ha has hq]
  have hi : i.castSucc ≤ Fin.last n := Nat.le_of_lt i.isLt
  have hindex : followupCavityIncidentIndex i=
      anisotropicOrderedCoupling i.castSucc (Fin.last n):=by
    apply Subtype.ext
    simp only [followupCavityIncidentIndex,anisotropicOrderedCoupling,
      min_eq_left hi,max_eq_right hi]
  have hspin : anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n)) z.2=
      Paper.spinSign (z.2 i.castSucc)*Paper.spinSign (z.2 (Fin.last n)):=by
    exact anisotropicOrderedCoupling_feature i.castSucc (Fin.last n) z.2
  rw [hindex]
  dsimp only
  rw [hspin]
  rfl

theorem cavityNativeFiveResponse_group (hn : 0<n)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (d : ℕ) (hd : d≤k+2)
    (z : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 nativeFive_zero_mem
    let P:=anisotropicProcessParameter D (Paper.parisiSchemeMeasure s)
      (anisotropicSchemeNode s (k+2-d) (by omega)) z.1
    let w:=cavityOuterStieltjesWeight (anisotropicSchemeMass s) a (k+1)
    let Pr:=cavityNativeResponseChargeParameter D s z.1
    let Fbar:=cavityNativeResponseLastCentered D s a d P
    let Abar:=cavityNativeResponseRestCentered D s a d P
    ((n:ℝ)⁻¹/2)*(∑i : Fin n,cavityFixedRowNativeFiniteResponseIntegrand D s a d hd i z)=
      cavityFiniteLastObservableGroupedValue s n β ρ hβ hρ d P w
        (cavityNativeResponseChargeDepth k) Pr z.2 Abar+
      cavityFiniteRestObservableGroupedValue s n β ρ hβ hρ d P w
        (cavityNativeResponseChargeDepth k) Pr z.2 Fbar+
      cavityFiniteIncidentFreeDensityGroupedValue s n β ρ hβ hρ a w
        (cavityNativeResponseChargeDepth k) Pr z.2 Fbar Abar :=by
  dsimp only
  simp_rw [native_response_integrand_eq_charge_five _ s a ha has hq d hd]
  exact cavityFiniteFiveResponse_group s hn β ρ hβ hρ a ha has hq d _
    (cavityOuterStieltjesWeight (anisotropicSchemeMass s) a (k+1))
    (cavityNativeResponseChargeDepth k) (fun r=>by dsimp only [cavityNativeResponseChargeDepth];omega)
    (cavityNativeResponseChargeParameter _ s z.1) z.2 _ _

end QuantitativeFollowup
