module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeChargeScores

@[expose] public section

/-! Literal finite feature means and Hessians at every signed outer charge
are the native responses at the actual charge node. The terminal and zero
charges remain separate, and every repeated atom keeps its genuine state. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem cavityNativeChargeFeature_eq_finite (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (r : Option (Option (Fin (k+1))))
    (e : AnisotropicCouplingIndex n) (sample : AnisotropicDisorderBrownianSample n) :
    anisotropicProcessPairResponse D (Paper.parisiSchemeMeasure s)
      (cavityOuterSchemeChargeNode s r) e sample=
      anisotropicFiniteFeatureMean D s (k+2-cavityOuterChargePosition (k+1) r)
        (anisotropicPairFeature e) (anisotropicProcessParameter D (Paper.parisiSchemeMeasure s)
          (cavityOuterSchemeChargeNode s r) sample) :=by
  rw [cavityOuterSchemeChargeNode_eq_position]
  exact (cavityFiniteEnergyPairMean_at_native_scheme_node D s _
    (cavityOuterSchemeChargePosition_le r) e sample).symm.trans
      (cavityFiniteEnergyFeatureMean_at_parameter D s _ _ _)

theorem cavityNativeChargeSecond_eq_finite (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (r : Option (Option (Fin (k+1))))
    (e : AnisotropicCouplingIndex n) (sample : AnisotropicDisorderBrownianSample n) :
    anisotropicProcessPairSecond D (Paper.parisiSchemeMeasure s)
      (cavityOuterSchemeChargeNode s r) e sample=
      anisotropicFinitePairSecond D s (k+2-cavityOuterChargePosition (k+1) r)
        (anisotropicProcessParameter D (Paper.parisiSchemeMeasure s)
          (cavityOuterSchemeChargeNode s r) sample) e :=by
  rw [cavityOuterSchemeChargeNode_eq_position]
  exact (cavityFiniteEnergyRowSecond_at_native_scheme_node D s _
    (cavityOuterSchemeChargePosition_le r) e sample).symm.trans
      (cavityFiniteEnergyRowSecond_at_parameter D s _ _ _)

theorem integral_cavityNativeChargeFeature_eq_finite_sum (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (e : AnisotropicCouplingIndex n) (sample : AnisotropicDisorderBrownianSample n) :
    (∫r,anisotropicProcessPairResponse D (Paper.parisiSchemeMeasure s) r e sample
      ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)=
      ∑r : Option (Option (Fin (k+1))),
        cavityOuterStieltjesWeight (anisotropicSchemeMass s) a (k+1) r*
        anisotropicFiniteFeatureMean D s (k+2-cavityOuterChargePosition (k+1) r)
          (anisotropicPairFeature e) (anisotropicProcessParameter D (Paper.parisiSchemeMeasure s)
            (cavityOuterSchemeChargeNode s r) sample) :=by
  rw [←cavityOuterSchemeCharge_sum_eq_actual_free s a ha has hq
    (fun r=>anisotropicProcessPairResponse D (Paper.parisiSchemeMeasure s) r e sample)]
  simp_rw [cavityNativeChargeFeature_eq_finite]

theorem integral_cavityNativeChargeSecond_eq_finite_sum (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (e : AnisotropicCouplingIndex n) (sample : AnisotropicDisorderBrownianSample n) :
    (∫r,anisotropicProcessPairSecond D (Paper.parisiSchemeMeasure s) r e sample
      ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)=
      ∑r : Option (Option (Fin (k+1))),
        cavityOuterStieltjesWeight (anisotropicSchemeMass s) a (k+1) r*
        anisotropicFinitePairSecond D s (k+2-cavityOuterChargePosition (k+1) r)
          (anisotropicProcessParameter D (Paper.parisiSchemeMeasure s)
            (cavityOuterSchemeChargeNode s r) sample) e :=by
  rw [←cavityOuterSchemeCharge_sum_eq_actual_free s a ha has hq
    (fun r=>anisotropicProcessPairSecond D (Paper.parisiSchemeMeasure s) r e sample)]
  simp_rw [cavityNativeChargeSecond_eq_finite]

end QuantitativeFollowup
