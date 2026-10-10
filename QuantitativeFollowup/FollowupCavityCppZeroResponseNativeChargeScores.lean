module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeSchemeFeature
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterHistoryScores
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterSchemeStieltjes

@[expose] public section

/-! The complete finite posterior charges are the actual native feature
responses at the original nodes. Their signed sum is the genuine free
Stieltjes integral, retaining the root atom and repeated nodes. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityOuterSchemeChargePosition_le (i : Option (Option (Fin (k+1)))) :
    cavityOuterChargePosition (k+1) i ≤ k+2 :=by
  cases i with
  | none=>simp only [cavityOuterChargePosition];omega
  | some i=>cases i with
    | none=>simp only [cavityOuterChargePosition];omega
    | some i=>simp only [cavityOuterChargePosition];have hi:=i.isLt;omega

theorem cavityOuterSchemeChargeNode_eq_position (s : RSBScheme k)
    (i : Option (Option (Fin (k+1)))) :
    cavityOuterSchemeChargeNode s i=
      anisotropicSchemeNode s (cavityOuterChargePosition (k+1) i)
        (cavityOuterSchemeChargePosition_le i) :=by
  cases i with
  | none=>apply Subtype.ext;exact s.q_top.symm
  | some i=>cases i with
    | none=>apply Subtype.ext;exact s.q_zero.symm
    | some i=>rfl

private theorem charge_position_fin (i : Option (Option (Fin (k+1)))) :
    Fin.ofNat (k+3) (cavityOuterChargePosition (k+1) i)=
      (⟨cavityOuterChargePosition (k+1) i,by have hi:=cavityOuterSchemeChargePosition_le i;omega⟩ : Fin (k+3)) :=by
  apply Fin.ext
  change cavityOuterChargePosition (k+1) i % (k+3)=cavityOuterChargePosition (k+1) i
  rw [Nat.mod_eq_of_lt]
  have hi:=cavityOuterSchemeChargePosition_le i
  omega

theorem cavityOuterNativeCharge_first (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Option (Option (Fin (k+1)))) (e : AnisotropicCouplingIndex n)
    (sample : AnisotropicDisorderBrownianSample n) :
    fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
      (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s)
      (k+2-cavityOuterChargePosition (k+1) i))
      (cavitySchemeEnergyHistoryProjection D (cavityNativeSchemeHistory D s sample)
        (Fin.ofNat (k+3) (cavityOuterChargePosition (k+1) i))) (anisotropicPairFeature e)=
      anisotropicProcessPairResponse D (Paper.parisiSchemeMeasure s)
        (cavityOuterSchemeChargeNode s i) e sample :=by
  rw [charge_position_fin]
  change cavityFiniteEnergyFeatureMean (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
    (cavityFiniteEnergyInput D s) (k+2-cavityOuterChargePosition (k+1) i) (anisotropicPairFeature e)
      (anisotropicEnergyMap D (anisotropicProcessParameter D (Paper.parisiSchemeMeasure s)
        (anisotropicSchemeNode s (cavityOuterChargePosition (k+1) i)
          (cavityOuterSchemeChargePosition_le i)) sample))=_
  rw [cavityFiniteEnergyPairMean_at_native_scheme_node,←cavityOuterSchemeChargeNode_eq_position]

theorem cavityOuterNativeCharge_second (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : Option (Option (Fin (k+1)))) (e : AnisotropicCouplingIndex n)
    (sample : AnisotropicDisorderBrownianSample n) :
    fderiv ℝ (fun H=>fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
      (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s)
      (k+2-cavityOuterChargePosition (k+1) i)) H (anisotropicPairFeature e))
      (cavitySchemeEnergyHistoryProjection D (cavityNativeSchemeHistory D s sample)
        (Fin.ofNat (k+3) (cavityOuterChargePosition (k+1) i))) (anisotropicPairFeature e)=
      anisotropicProcessPairSecond D (Paper.parisiSchemeMeasure s)
        (cavityOuterSchemeChargeNode s i) e sample :=by
  rw [charge_position_fin]
  change cavityFiniteEnergyRowSecond (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
    (cavityFiniteEnergyInput D s) (k+2-cavityOuterChargePosition (k+1) i) (anisotropicPairFeature e)
      (anisotropicEnergyMap D (anisotropicProcessParameter D (Paper.parisiSchemeMeasure s)
        (anisotropicSchemeNode s (cavityOuterChargePosition (k+1) i)
          (cavityOuterSchemeChargePosition_le i)) sample))=_
  rw [cavityFiniteEnergyRowSecond_at_native_scheme_node,←cavityOuterSchemeChargeNode_eq_position]

theorem cavityOuterNativeCharge_first_sum (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (e : AnisotropicCouplingIndex n) (sample : AnisotropicDisorderBrownianSample n) :
    (∑i,cavityOuterStieltjesWeight (anisotropicSchemeMass s) a (k+1) i*
      fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
        (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s)
        (k+2-cavityOuterChargePosition (k+1) i))
        (cavitySchemeEnergyHistoryProjection D (cavityNativeSchemeHistory D s sample)
          (Fin.ofNat (k+3) (cavityOuterChargePosition (k+1) i))) (anisotropicPairFeature e))=
      ∫r,anisotropicProcessPairResponse D (Paper.parisiSchemeMeasure s) r e sample
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a :=by
  simp_rw [cavityOuterNativeCharge_first]
  exact cavityOuterSchemeCharge_sum_eq_actual_free s a ha has hq
    (fun r => anisotropicProcessPairResponse D (Paper.parisiSchemeMeasure s) r e sample)

theorem cavityOuterNativeCharge_second_sum (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (e : AnisotropicCouplingIndex n) (sample : AnisotropicDisorderBrownianSample n) :
    (∑i,cavityOuterStieltjesWeight (anisotropicSchemeMass s) a (k+1) i*
      fderiv ℝ (fun H=>fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
        (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s)
        (k+2-cavityOuterChargePosition (k+1) i)) H (anisotropicPairFeature e))
        (cavitySchemeEnergyHistoryProjection D (cavityNativeSchemeHistory D s sample)
          (Fin.ofNat (k+3) (cavityOuterChargePosition (k+1) i))) (anisotropicPairFeature e))=
      ∫r,anisotropicProcessPairSecond D (Paper.parisiSchemeMeasure s) r e sample
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a :=by
  simp_rw [cavityOuterNativeCharge_second]
  exact cavityOuterSchemeCharge_sum_eq_actual_free s a ha has hq
    (fun r => anisotropicProcessPairSecond D (Paper.parisiSchemeMeasure s) r e sample)

end QuantitativeFollowup
