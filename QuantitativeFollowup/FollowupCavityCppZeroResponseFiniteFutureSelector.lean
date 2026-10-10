module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseRowJets
public import QuantitativeFollowup.AnisotropicVarianceRestartNodeSquare
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFutureAgreementScalar
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFutureAgreementRest

@[expose] public section

/-! The binary-feature future selector in the exact finite Stieltjes
formula is the actual scalar/rest continuation at each original node.
Repeated levels are handled by the genuine zero-segment pair-moment law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets OverlapPaper
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityFiniteIncidentPairMoment_eq_parameter_expectation
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (p j : ℕ)
    (P : AnisotropicParameter (n+1)) (i : Fin n) :
    finiteStateCascadePairMoment (fun _ : QuantitativePaper.Configuration (n+1)=>0)
      (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) p j (anisotropicEnergyMap D P)
      (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n)))
      (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n)))=
      sourceKernelExpectation (fun r=>anisotropicDepthKernel D s (p+r)) j
        (fun Q=>(anisotropicFiniteFeatureMean D s p
          (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))) Q)^2) P :=by
  let K:=anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))
  let G : FiniteStateField (QuantitativePaper.Configuration (n+1))→ℝ:=fun H=>
    (∫σ,K σ ∂finiteStateCascadeGibbsKernel (fun _ : QuantitativePaper.Configuration (n+1)=>0)
      (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) p H)^2
  have hG:Measurable G:=
    ((measurable_of_finite K).stronglyMeasurable.integral_kernel.measurable).pow_const 2
  have he:=sourceKernelExpectation_finiteStateCascade_comp_linear (anisotropicEnergyMap D)
    (anisotropicSchemeInput D s) (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (SpinGlass.AT.gtStateLogPartition (fun _ : QuantitativePaper.Configuration (n+1)=>0))
    (finiteStateGaussianTerminal_lipschitz (fun _ : QuantitativePaper.Configuration (n+1)=>0)) p j G hG P
  rw [←anisotropicDepthKernel_eq_parameterCascadeKernel D s] at he
  have hL:(fun r=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s r))=
      cavityFiniteEnergyInput D s:=rfl
  rw [hL] at he
  have hmean:(fun Q=>G (anisotropicEnergyMap D Q))=fun Q=>
      (anisotropicFiniteFeatureMean D s p K Q)^2:=by funext Q;rfl
  rw [hmean] at he
  unfold finiteStateCascadePairMoment
  simp_rw [fderiv_finiteStateGaussianTerminalCascade_eq_gibbsMean _ _
    (anisotropicSchemeMass_nonneg s)]
  simpa only [G,K,pow_two] using he

theorem cavityFiniteIncidentFutureSquare_node_zero (s : RSBScheme k) (n : ℕ)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (J p : ℕ)
    (hJ : J≤k+2) (hp : p≤J) (P : AnisotropicParameter (n+1)) (i : Fin n) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    cavityFiniteFutureSquare D s J (anisotropicEnergyMap D P)
      (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n)))
      (scalarSchemeTransportNode s (k+2-p))=
      cavityFiniteRowFutureRestSquare s n β ρ hβ hρ p (J-p) i
        (cavityRestParameterProjection n P)*
      cavityFiniteRowFutureScalarSquare s (followupCavityScalarBeta n β ρ) p (J-p)
        (P (Sum.inr (Fin.last n))) :=by
  dsimp only
  rw [cavityFiniteFutureSquare_node _ s J p hJ hp,
    cavityFiniteIncidentPairMoment_eq_parameter_expectation,
    cavityFiniteRowFutureSquare_zero]

end QuantitativeFollowup
