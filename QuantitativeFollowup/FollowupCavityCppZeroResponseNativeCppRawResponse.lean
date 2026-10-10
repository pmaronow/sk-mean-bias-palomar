module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeResponseIntegral
public import QuantitativeFollowup.FollowupCavityFixedRowNativeCppAgreement

@[expose] public section

/-! The native covariance's genuine right derivative at the independent
endpoint is the actual five-term posterior response. The full retained
history and terminal mark are transported to the native scheme process
before the scalar/rest expectation contraction. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon.FiniteStreamingPolynomials
open SpinGlass.Targets
variable {n k : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

 theorem nativeCppRaw_zero_mem : (0:ℝ)∈Icc 0 1 := ⟨le_rfl,zero_le_one⟩

theorem native_cpp_firstJet_scheme_zero_eq_native_raw_response
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (d : ℕ) (hd : d≤k+2) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 nativeCppRaw_zero_mem
    withinJet (followupCavityCppFunction n β ρ hβ hρ (Paper.parisiSchemeMeasure s) a
      (anisotropicSchemeNode s (k+2-d) (by omega))) (Icc (0:ℝ) 1) 1 0=
      followupCavityAlpha n β ρ/(2*(n:ℝ))*
        ∑i : Fin n,∫p,cavityFixedRowNativeFiniteResponseIntegrand D s a d hd i p
          ∂anisotropicMeasureSpinPathLaw D (Paper.parisiSchemeMeasure s) a :=by
  rw [←derivWithin_cavityFixedRowPhysicalCurveCovariance_eq_native_cpp β ρ hβ hρ s a d hd
    0 nativeCppRaw_zero_mem]
  exact derivWithin_cavityFixedRowPhysicalCurveCovariance_native_response
    hn β ρ hβ hρ s a ha has hq d hd

end QuantitativeFollowup
