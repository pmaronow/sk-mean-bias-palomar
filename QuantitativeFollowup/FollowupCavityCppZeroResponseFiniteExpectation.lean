module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeFiveGrouping
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeFiveResponseIntegral
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeLastGrouping
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeRestGrouping
public import QuantitativeFollowup.FollowupCavityCppZeroResponseRestEvaluation
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeDensityGrouping

@[expose] public section

/-! The genuine finite covariance derivative is split into its three
actual marked expectations. Integrability is obtained from the constructed
last, rest, and density response data, including every signed root charge. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon.FiniteStreamingPolynomials
open SpinGlass.Targets
variable {n k : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 theorem finiteExpectation_zero_mem : (0:ℝ)∈Icc 0 1:=⟨le_rfl,zero_le_one⟩

theorem cavityNativeFiveResponse_eq_actual_groups
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (d : ℕ) (hd : d≤k+2)
    (z : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 finiteExpectation_zero_mem
    let μ:=Paper.parisiSchemeMeasure s
    let p:=anisotropicSchemeNode s (k+2-d) (by omega)
    ((n:ℝ)⁻¹/2)*(∑i : Fin n,cavityFixedRowNativeFiniteResponseIntegrand D s a d hd i z)=
      cavityZeroLastResponseIntegrand μ n β ρ hβ hρ a p z+
      cavityZeroRestResponseIntegrand μ n β ρ hβ hρ a p z+
      cavityZeroDensityResponseIntegrand μ n β ρ hβ hρ a p z:=by
  have h:=cavityNativeFiveResponse_group hn β ρ hβ hρ s a ha has hq d hd z
  dsimp only at h ⊢
  rw [cavityFiniteLastObservableGroupedValue_at_native s n β ρ hβ hρ a ha has hq d hd z,
    cavityFiniteRestObservableGroupedValue_at_native s n β ρ hβ hρ a ha has hq d hd z,
    cavityFiniteIncidentFreeDensityGroupedValue_at_native s n β ρ hβ hρ a ha has hq d hd z] at h
  exact h

theorem native_cpp_firstJet_scheme_zero_eq_three_expectations
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (d : ℕ) (hd : d≤k+2) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 finiteExpectation_zero_mem
    let μ:=Paper.parisiSchemeMeasure s
    let p:=anisotropicSchemeNode s (k+2-d) (by omega)
    let P:=anisotropicMeasureSpinPathLaw D μ a
    withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc (0:ℝ) 1) 1 0=
      followupCavityAlpha n β ρ*
        ((∫z,cavityZeroLastResponseIntegrand μ n β ρ hβ hρ a p z ∂P)+
          (∫z,cavityZeroRestResponseIntegrand μ n β ρ hβ hρ a p z ∂P)+
          (∫z,cavityZeroDensityResponseIntegrand μ n β ρ hβ hρ a p z ∂P)):=by
  dsimp only
  let μ:=Paper.parisiSchemeMeasure s
  let p:=anisotropicSchemeNode s (k+2-d) (by omega)
  have hL:=(cavityZeroLastResponseIntegrand_data s n β ρ hβ hρ a ha has hq p).1
  have hR:=(cavityZeroRestResponseIntegrand_data s n β ρ hβ hρ a ha has hq p).1
  have hD:=(cavityZeroDensityResponseIntegrand_data s n β ρ hβ hρ a ha has hq p).1
  rw [native_cpp_firstJet_scheme_zero_eq_five_response_integral hn β ρ hβ hρ s a ha has hq d hd]
  simp_rw [cavityNativeFiveResponse_eq_actual_groups hn β ρ hβ hρ s a ha has hq d hd]
  rw [integral_add
    (f:=fun z=>cavityZeroLastResponseIntegrand μ n β ρ hβ hρ a p z+
      cavityZeroRestResponseIntegrand μ n β ρ hβ hρ a p z)
    (g:=fun z=>cavityZeroDensityResponseIntegrand μ n β ρ hβ hρ a p z) (hL.add hR) hD,
    integral_add (f:=fun z=>cavityZeroLastResponseIntegrand μ n β ρ hβ hρ a p z)
      (g:=fun z=>cavityZeroRestResponseIntegrand μ n β ρ hβ hρ a p z) hL hR]

end QuantitativeFollowup
