module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNodeStieltjesSpatial

@[expose] public section

/-! Parameter-space differentiation of the actual binary-feature node
response. The current right CDF and the literal strict-future free integral
are both retained; the pullback uses genuine smooth finite potentials. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper
open scoped ContDiff
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem cavityFinitePairSecond_free_parameter_spatial
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (J : ℕ) (hJ : J≤k+2)
    (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (e : AnisotropicCouplingIndex n) (P v : AnisotropicParameter n) :
    fderiv ℝ (fun Q=>anisotropicFinitePairSecond D s J Q e) P v=
      -2*Paper.parisiCDF (Paper.parisiSchemeMeasure s)
        (scalarSchemeTransportNode s (k+2-J))*anisotropicFiniteFeatureMean D s J
          (anisotropicPairFeature e) P*
        fderiv ℝ (anisotropicFiniteFeatureMean D s J (anisotropicPairFeature e)) P v-
      ∫r,if scalarSchemeTransportNode s (k+2-J)<r then
        fderiv ℝ (fun Q=>cavityFiniteFutureSquare D s J (anisotropicEnergyMap D Q)
          (anisotropicPairFeature e) r) P v else 0
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a :=by
  let U:=finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
    (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) J
  let K:=anisotropicPairFeature e
  let A:=fun H=>exponentialDensityHessian U H K K
  let M:=cavityFiniteEnergyFeatureMean (fun _ : Configuration n=>0)
    (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) J K
  let L:=anisotropicEnergyMap D
  have hU:ContDiff ℝ ∞ U:=contDiff_finiteStateGaussianTerminalCascade
    (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
    (anisotropicSchemeMass_nonneg s) (cavityFiniteEnergyInput D s) J
  have hA:ContDiff ℝ ∞ A:=by
    have hD₁:ContDiff ℝ ∞ (fderiv ℝ U):=hU.fderiv_right (by simp)
    have hD₂:ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ U)):=hD₁.fderiv_right (by simp)
    exact (hD₂.clm_apply contDiff_const).clm_apply contDiff_const
  have hM:ContDiff ℝ ∞ M:=(boundedJets_cavityFiniteEnergyFeatureMean
    (fun _ : Configuration n=>0) (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (cavityFiniteEnergyInput D s) J K).1
  have heA:(fun Q=>anisotropicFinitePairSecond D s J Q e)=A ∘ L:=by
    funext Q
    exact anisotropicFinitePairSecond_eq_energy D s J Q e
  have heM:anisotropicFiniteFeatureMean D s J K=M ∘ L:=by
    funext Q
    exact (cavityFiniteEnergyFeatureMean_at_parameter D s J K Q).symm
  have hdA:=((hA.differentiable (by simp) (L P)).hasFDerivAt).comp P L.hasFDerivAt
  have hdM:=((hM.differentiable (by simp) (L P)).hasFDerivAt).comp P L.hasFDerivAt
  rw [heA,hdA.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [cavityFiniteBinaryHessian_free_spatial D s J hJ a ha has hq K
    (anisotropicPairFeature_binary e) (L P) (L v)]
  rw [heM,hdM.fderiv]
  simp only [Function.comp_def,ContinuousLinearMap.comp_apply]
  congr 1
  apply integral_congr_ae
  exact .of_forall fun r=>by
    dsimp only
    split_ifs with hr
    · have hF:=contDiff_cavityFiniteFutureSquare_field D s J K r
      have hdF:=((hF.differentiable (by simp) (L P)).hasFDerivAt).comp P L.hasFDerivAt
      change _=(fderiv ℝ ((fun H=>cavityFiniteFutureSquare D s J H K r) ∘ L) P) v
      rw [hdF.fderiv]
      rfl
    · rfl

end QuantitativeFollowup
