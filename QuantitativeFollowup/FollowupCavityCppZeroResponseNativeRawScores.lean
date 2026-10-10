module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeChargeScores
public import QuantitativeFollowup.FollowupCavityCppZeroResponsePhysicalRawScore

@[expose] public section

/-! The raw finite response score is transported through the complete native
marked-history law. Its charges are actual native first and second feature
responses integrated against the free overlap measure. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityFixedRowHistoryRawScore (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (i : Fin n)
    (p : FiniteHistory (FiniteStateField (Configuration (n+1))) (k+2)×Configuration (n+1)) : ℝ :=
  let K:=anisotropicPairFeature (followupCavityIncidentIndex i)
  K p.2-∑r,cavityOuterStieltjesWeight (anisotropicSchemeMass s) a (k+1) r*
    cavityFiniteEnergyFeatureMean (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s)
      (cavityFiniteEnergyInput D s) (k+2-cavityOuterChargePosition (k+1) r) K
      (p.1 (Fin.ofNat (k+3) (cavityOuterChargePosition (k+1) r)))

def cavityFixedRowHistoryRawSecond (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (i : Fin n)
    (p : FiniteHistory (FiniteStateField (Configuration (n+1))) (k+2)×Configuration (n+1)) : ℝ :=
  let K:=anisotropicPairFeature (followupCavityIncidentIndex i)
  ∑r,cavityOuterStieltjesWeight (anisotropicSchemeMass s) a (k+1) r*
    cavityFiniteEnergyRowSecond (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s)
      (cavityFiniteEnergyInput D s) (k+2-cavityOuterChargePosition (k+1) r) K
      (p.1 (Fin.ofNat (k+3) (cavityOuterChargePosition (k+1) r)))

theorem cavityFixedRowRawScore_eq_history (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (i : Fin n)
    (p : AnisotropicDisorder (n+1)×((Fin (k+2)→QuantitativePaper.Field (n+1))×Configuration (n+1))) :
    cavityFixedRowRawScore D s a i p=cavityFixedRowHistoryRawScore D s a i
      (cavityOuterHistoryMap (cavityFiniteEnergyInput D s) (k+2) (anisotropicRootEnergyMap D) 0 p) :=by
  unfold cavityFixedRowRawScore cavityFixedRowHistoryRawScore
  simp_rw [cavityOuterStieltjesPotential_first_eq_history]
  rfl

theorem cavityFixedRowRawSecond_eq_history (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (i : Fin n)
    (p : AnisotropicDisorder (n+1)×((Fin (k+2)→QuantitativePaper.Field (n+1))×Configuration (n+1))) :
    cavityFixedRowRawSecond D s a i p=cavityFixedRowHistoryRawSecond D s a i
      (cavityOuterHistoryMap (cavityFiniteEnergyInput D s) (k+2) (anisotropicRootEnergyMap D) 0 p) :=by
  unfold cavityFixedRowRawSecond cavityFixedRowHistoryRawSecond
  simp_rw [cavityOuterStieltjesPotential_second_eq_history]
  rfl

theorem measurable_cavityFixedRowHistoryRawScore (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (i : Fin n) :
    Measurable (cavityFixedRowHistoryRawScore D s a i) :=by
  unfold cavityFixedRowHistoryRawScore
  refine ((measurable_of_finite (fun σ : Configuration (n+1)=>
    anisotropicPairFeature (followupCavityIncidentIndex i) σ)).comp measurable_snd).sub ?_
  apply Finset.measurable_sum
  intro r _
  apply Measurable.const_mul
  exact (boundedJets_cavityFiniteEnergyFeatureMean (fun _ : Configuration (n+1)=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) (cavityFiniteEnergyInput D s)
    (k+2-cavityOuterChargePosition (k+1) r) (anisotropicPairFeature (followupCavityIncidentIndex i))).1.continuous.measurable.comp
      ((measurable_pi_apply _).comp measurable_fst)

theorem measurable_cavityFixedRowHistoryRawSecond (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (i : Fin n) :
    Measurable (cavityFixedRowHistoryRawSecond D s a i) :=by
  unfold cavityFixedRowHistoryRawSecond
  apply Finset.measurable_sum
  intro r _
  apply Measurable.const_mul
  have hU:=contDiff_finiteStateGaussianTerminalCascade (fun _ : Configuration (n+1)=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) (cavityFiniteEnergyInput D s)
    (k+2-cavityOuterChargePosition (k+1) r)
  have hD : ContDiff ℝ ∞ (fun H=>fderiv ℝ
      (finiteStateGaussianTerminalCascade (fun _ : Configuration (n+1)=>0)
        (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s)
        (k+2-cavityOuterChargePosition (k+1) r)) H
      (anisotropicPairFeature (followupCavityIncidentIndex i))) :=
    (hU.fderiv_right (by simp)).clm_apply
    (contDiff_const (c:=anisotropicPairFeature (followupCavityIncidentIndex i)))
  have hDD : ContDiff ℝ ∞ (cavityFiniteEnergyRowSecond
      (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s)
      (k+2-cavityOuterChargePosition (k+1) r)
      (anisotropicPairFeature (followupCavityIncidentIndex i))) :=
    (hD.fderiv_right (by simp)).clm_apply
    (contDiff_const (c:=anisotropicPairFeature (followupCavityIncidentIndex i)))
  exact hDD.continuous.measurable.comp ((measurable_pi_apply _).comp measurable_fst)

theorem cavityFixedRowHistoryRawScore_at_native (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (i : Fin n) (p : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)) :
    cavityFixedRowHistoryRawScore D s a i
      (cavitySchemeEnergyHistoryProjection D (cavityNativeSchemeHistory D s p.1),p.2)=
      anisotropicPairFeature (followupCavityIncidentIndex i) p.2-
        ∫r,anisotropicProcessPairResponse D (Paper.parisiSchemeMeasure s) r
          (followupCavityIncidentIndex i) p.1 ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a :=by
  unfold cavityFixedRowHistoryRawScore
  dsimp only
  simp only [cavityFiniteEnergyFeatureMean]
  rw [cavityOuterNativeCharge_first_sum D s a ha has hq]

theorem cavityFixedRowHistoryRawSecond_at_native (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (i : Fin n) (p : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)) :
    cavityFixedRowHistoryRawSecond D s a i
      (cavitySchemeEnergyHistoryProjection D (cavityNativeSchemeHistory D s p.1),p.2)=
      ∫r,anisotropicProcessPairSecond D (Paper.parisiSchemeMeasure s) r
        (followupCavityIncidentIndex i) p.1 ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a :=by
  unfold cavityFixedRowHistoryRawSecond
  exact cavityOuterNativeCharge_second_sum D s a ha has hq _ _

end QuantitativeFollowup
