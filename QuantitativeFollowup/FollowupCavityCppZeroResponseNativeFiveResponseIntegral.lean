module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeCppRawResponse
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeResponseIntegrability

@[expose] public section

/-! The genuine native first jet is an expectation of the complete
normalized five-term response, at every original finite-profile node.
The finite sum is interchanged only after proving actual integrability. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon.FiniteStreamingPolynomials
open SpinGlass.Targets
variable {n k : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

 theorem nativeFiveIntegral_zero_mem : (0:ℝ)∈Icc 0 1 := ⟨le_rfl,zero_le_one⟩

theorem native_cpp_firstJet_scheme_zero_eq_five_response_integral
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (d : ℕ) (hd : d≤k+2) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 nativeFiveIntegral_zero_mem
    withinJet (followupCavityCppFunction n β ρ hβ hρ (Paper.parisiSchemeMeasure s) a
      (anisotropicSchemeNode s (k+2-d) (by omega))) (Icc (0:ℝ) 1) 1 0=
      followupCavityAlpha n β ρ*
        (∫z,((n:ℝ)⁻¹/2)*(∑i : Fin n,
          cavityFixedRowNativeFiniteResponseIntegrand D s a d hd i z)
          ∂anisotropicMeasureSpinPathLaw D (Paper.parisiSchemeMeasure s) a) :=by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 nativeFiveIntegral_zero_mem
  have hi (i : Fin n) : Integrable
      (cavityFixedRowNativeFiniteResponseIntegrand D s a d hd i)
      (anisotropicMeasureSpinPathLaw D (Paper.parisiSchemeMeasure s) a) :=
    integrable_cavityFixedRowNativeFiniteResponseIntegrand s n β ρ hβ hρ a ha has hq d hd i
  rw [native_cpp_firstJet_scheme_zero_eq_native_raw_response hn β ρ hβ hρ s a ha has hq d hd]
  rw [←integral_finset_sum Finset.univ (fun i _=>hi i),integral_const_mul]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end QuantitativeFollowup
