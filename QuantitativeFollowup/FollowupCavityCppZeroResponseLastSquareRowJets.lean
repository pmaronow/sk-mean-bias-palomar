module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseRowSquaredJets
public import QuantitativeFollowup.FollowupCavityCppZeroResponseRowObservableJets
public import QuantitativeFollowup.FollowupCavityCppZeroResponseLastVarianceFeatures
public import FourPapersCommon.ExponentialDensityHessian

@[expose] public section

/-! Literal isolated-spin square row jets. Its second row derivative is
the last spatial derivative of the genuine binary-feature row Hessian Wi. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

private theorem smooth_cavityFiniteEnergyRowSecond (V : QuantitativePaper.Configuration n→ℝ)
    (a : ℕ→ℝ) (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField (QuantitativePaper.Configuration n))
    (j : ℕ) (K : FiniteStateField (QuantitativePaper.Configuration n)) :
    ContDiff ℝ ∞ (cavityFiniteEnergyRowSecond V a L j K) :=by
  have hU:=contDiff_finiteStateGaussianTerminalCascade V a ha L j
  have hD:ContDiff ℝ ∞ (fun Q=>fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) Q K):=
    (hU.fderiv_right (by simp)).clm_apply (contDiff_const (c:=K))
  exact (hD.fderiv_right (by simp)).clm_apply (contDiff_const (c:=K))

theorem cavityFiniteEnergyRowSecond_at_parameter (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (e : AnisotropicCouplingIndex n) (P : AnisotropicParameter n) :
    cavityFiniteEnergyRowSecond (fun _ : QuantitativePaper.Configuration n=>0) (anisotropicSchemeMass s)
      (cavityFiniteEnergyInput D s) j (anisotropicPairFeature e) (anisotropicEnergyMap D P)=
      anisotropicFinitePairSecond D s j P e :=by
  have hU:=contDiff_finiteStateGaussianTerminalCascade (fun _ : QuantitativePaper.Configuration n=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) (cavityFiniteEnergyInput D s) j
  unfold cavityFiniteEnergyRowSecond
  rw [(hasFDerivAt_exponential_directional_field _ (hU.of_le (by simp))
    (anisotropicEnergyMap D P) (anisotropicPairFeature e)).fderiv,ContinuousLinearMap.flip_apply]
  exact (anisotropicFinitePairSecond_eq_energy D s j P e).symm

theorem fderiv_cavityFiniteEnergyRowSecond_at_parameter (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (e : AnisotropicCouplingIndex n)
    (P delta : AnisotropicParameter n) :
    fderiv ℝ (cavityFiniteEnergyRowSecond (fun _ : QuantitativePaper.Configuration n=>0)
      (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) j (anisotropicPairFeature e))
      (anisotropicEnergyMap D P) (anisotropicEnergyMap D delta)=
      fderiv ℝ (fun Q=>anisotropicFinitePairSecond D s j Q e) P delta :=by
  have he : (fun Q=>anisotropicFinitePairSecond D s j Q e)=
      (cavityFiniteEnergyRowSecond (fun _ : QuantitativePaper.Configuration n=>0)
        (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) j (anisotropicPairFeature e)) ∘
          anisotropicEnergyMap D:=funext fun Q=>(cavityFiniteEnergyRowSecond_at_parameter D s j e Q).symm
  have hF:=smooth_cavityFiniteEnergyRowSecond (fun _ : QuantitativePaper.Configuration n=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) (cavityFiniteEnergyInput D s) j (anisotropicPairFeature e)
  rw [he,fderiv_comp P (hF.differentiable (by simp) _) (anisotropicEnergyMap D).differentiableAt,
    ContinuousLinearMap.fderiv,ContinuousLinearMap.comp_apply]

theorem cavityFiniteLastSquare_row_second (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (j : ℕ) (i : Fin n)
    (P : AnisotropicParameter (n+1)) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    let K:=anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))
    let b:=WithLp.toLp 2 (fun σ : QuantitativePaper.Configuration (n+1)=>Paper.spinSign (σ (Fin.last n)))
    fderiv ℝ (fun Q=>fderiv ℝ
      (fun R=>(cavityFiniteEnergyFeatureMean (fun _ : QuantitativePaper.Configuration (n+1)=>0)
        (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) j b R)^2) Q K)
      (anisotropicEnergyMap D P) K=
      2*(anisotropicFiniteFeatureMean (followupCavityRestSpinModel n β ρ hβ hρ) s j
          (fun σ=>Paper.spinSign (σ i)) (cavityRestParameterProjection n P)*
        parisiFSecond s (followupCavityScalarBeta n β ρ) j (P (Sum.inr (Fin.last n))))^2+
      2*parisiFDeriv s (followupCavityScalarBeta n β ρ) j (P (Sum.inr (Fin.last n)))*
        fderiv ℝ (fun Q=>anisotropicFinitePairSecond D s j Q
          (anisotropicOrderedCoupling i.castSucc (Fin.last n))) P
            (anisotropicCoordinateDirection (n+1) (Fin.last n)) :=by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
  let e:=anisotropicOrderedCoupling i.castSucc (Fin.last n)
  let b:FiniteStateField (QuantitativePaper.Configuration (n+1)):=WithLp.toLp 2
    (fun σ : QuantitativePaper.Configuration (n+1)=>Paper.spinSign (σ (Fin.last n)))
  have hb : anisotropicEnergyMap D (anisotropicCoordinateDirection (n+1) (Fin.last n))=b:=by
    ext σ
    exact anisotropicTerminalLinear_coordinate D σ (Fin.last n)
  have hm : cavityFiniteEnergyFeatureMean (fun _ : QuantitativePaper.Configuration (n+1)=>0)
      (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) j b (anisotropicEnergyMap D P)=
      parisiFDeriv s (followupCavityScalarBeta n β ρ) j (P (Sum.inr (Fin.last n))) :=by
    rw [cavityFiniteEnergyFeatureMean_eq_gibbsMean _ _ (anisotropicSchemeMass_nonneg s)]
    change anisotropicFiniteFeatureMean D s j (fun σ=>Paper.spinSign (σ (Fin.last n))) P=_
    simpa only [one_mul,anisotropicFiniteFeatureMean_one] using
      cavityFiniteIncidentFeature_zero s n β ρ hβ hρ j (fun _=>1) P
  rw [cavityFiniteEnergyFeatureSquare_second_row _ _ (anisotropicSchemeMass_nonneg s),
    cavityFiniteLastFeature_row_first s n β ρ hβ hρ j i P,hm]
  have hrow:=fderiv_cavityFiniteEnergyRowSecond_at_parameter D s j e P
    (anisotropicCoordinateDirection (n+1) (Fin.last n))
  rw [hb] at hrow
  rw [hrow]

end QuantitativeFollowup
