module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNodeStieltjes
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteFreeDerivative
public import QuantitativeFollowup.FollowupCavityCppZeroResponseRowSecondSpatialSmooth

@[expose] public section

/-! The derivative of the literal binary-feature Stieltjes identity is
taken against the actual finite free measure. The future integrands are
genuine smooth cascade expectations. No derivative/integral interchange
is assumed, and repeated atoms and the outer root charge are retained. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped ContDiff
namespace QuantitativeFollowup
open SpinGlass.Targets OverlapPaper
variable {n k : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem contDiff_cavityFiniteFutureSquare_field (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : ℕ) (K : FiniteStateField (QuantitativePaper.Configuration n))
    (r : Paper.Overlap) :
    ContDiff ℝ ∞ (fun H=>cavityFiniteFutureSquare D s J H K r) :=by
  let p:=cavityFiniteFutureDepth s J r
  let F:=fun H=>(cavityFiniteEnergyFeatureMean (fun _ : QuantitativePaper.Configuration n=>0)
    (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) p K H)^2
  have hmean:=boundedJets_cavityFiniteEnergyFeatureMean (fun _ : QuantitativePaper.Configuration n=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (cavityFiniteEnergyInput D s) p K
  have hF:BoundedJets F:=by
    simpa only [F,pow_two] using hmean.mul hmean
  have hc:=contDiff_cavityRowSecondSpatial_futureEnergy (fun _ : QuantitativePaper.Configuration n=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (anisotropicSchemeMass_le_one s 0)
    (antitone_nat_of_succ_le (anisotropicSchemeMass_antitone_step s))
    (cavityFiniteEnergyInput D s) p (J-p) F hF
  simpa only [cavityFiniteFutureSquare,finiteStateCascadePairMoment,F,p,
    cavityFiniteEnergyFeatureMean,pow_two] using hc

theorem contDiff_cavityFiniteFutureSquare_parameter (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : ℕ) (K : FiniteStateField (QuantitativePaper.Configuration n))
    (r : Paper.Overlap) :
    ContDiff ℝ ∞ (fun P=>cavityFiniteFutureSquare D s J (anisotropicEnergyMap D P) K r) :=
  (contDiff_cavityFiniteFutureSquare_field D s J K r).comp (anisotropicEnergyMap D).contDiff

theorem cavityFiniteBinaryHessian_free_spatial (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : ℕ) (hJ : J≤k+2)
    (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (K : FiniteStateField (QuantitativePaper.Configuration n)) (hK : ∀σ,K σ*K σ=1)
    (H v : FiniteStateField (QuantitativePaper.Configuration n)) :
    let U:=finiteStateGaussianTerminalCascade (fun _ : QuantitativePaper.Configuration n=>0)
      (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) J
    fderiv ℝ (fun Q=>exponentialDensityHessian U Q K K) H v=
      -2*Paper.parisiCDF (Paper.parisiSchemeMeasure s)
        (scalarSchemeTransportNode s (k+2-J))*
          cavityFiniteEnergyFeatureMean (fun _ : QuantitativePaper.Configuration n=>0)
            (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) J K H*
          fderiv ℝ (cavityFiniteEnergyFeatureMean (fun _ : QuantitativePaper.Configuration n=>0)
            (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) J K) H v-
      ∫r,if scalarSchemeTransportNode s (k+2-J)<r then
        fderiv ℝ (fun Q=>cavityFiniteFutureSquare D s J Q K r) H v else 0
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a :=by
  dsimp only
  let U:=finiteStateGaussianTerminalCascade (fun _ : QuantitativePaper.Configuration n=>0)
    (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) J
  let M:=cavityFiniteEnergyFeatureMean (fun _ : QuantitativePaper.Configuration n=>0)
    (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) J K
  let q:=scalarSchemeTransportNode s (k+2-J)
  let F:=fun Q r=>if q<r then cavityFiniteFutureSquare D s J Q K r else 0
  have hM:ContDiff ℝ ∞ M:=(boundedJets_cavityFiniteEnergyFeatureMean
    (fun _ : QuantitativePaper.Configuration n=>0) (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (cavityFiniteEnergyInput D s) J K).1
  have hF (r : Paper.Overlap):ContDiff ℝ ∞ (fun Q=>F Q r):=by
    dsimp only [F]
    split_ifs
    · exact contDiff_cavityFiniteFutureSquare_field D s J K r
    · exact contDiff_const
  have he:(fun Q=>exponentialDensityHessian U Q K K)=
      fun Q=>1-Paper.parisiCDF (Paper.parisiSchemeMeasure s) q*(M Q)^2-
        ∫r,F Q r ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a :=by
    funext Q
    exact cavityFiniteBinaryFeature_node_free_stieltjes D s J hJ a ha has hq Q K hK
  have hm:=(hM.differentiable (by simp) H).hasFDerivAt
  have hf:=hasFDerivAt_cavityFiniteFreeIntegral s a ha has hq F
    (fun r=>fderiv ℝ (fun Q=>F Q r) H) H
    (fun r=>((hF r).differentiable (by simp) H).hasFDerivAt)
  have hd:=(((hm.pow 2).const_mul (Paper.parisiCDF (Paper.parisiSchemeMeasure s) q)).const_sub 1).sub hf
  simp only [Pi.sub_def] at hd
  rw [←he] at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul,Nat.cast_ofNat,pow_one,
    ContinuousLinearMap.sum_apply]
  rw [cavityOuterSchemeCharge_sum_eq_actual_free s a ha has hq
    (fun r=>fderiv ℝ (fun Q=>F Q r) H v)]
  have hdf (r : Paper.Overlap):fderiv ℝ (fun Q=>F Q r) H v=
      if q<r then fderiv ℝ (fun Q=>cavityFiniteFutureSquare D s J Q K r) H v else 0 :=by
    dsimp only [F]
    by_cases hr:q<r
    · simp only [if_pos hr]
    · simp only [if_neg hr]
      rw [(hasFDerivAt_const (0:ℝ) H).fderiv]
      rfl
  simp_rw [hdf]
  dsimp only [M,q]
  simp only [show (2:ℕ)-1=1 from rfl,pow_one,two_smul]
  ring

end QuantitativeFollowup
