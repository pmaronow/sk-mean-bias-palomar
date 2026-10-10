module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseRowCovarianceCentering
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterResponseIntegrability
public import QuantitativeFollowup.FollowupCavityCppZeroResponsePhysicalRowIntegral

@[expose] public section

/-! The actual log-normalizer second derivative disappears from the genuine
response integral because its centered product has zero mean. Integrability
of both the original and the resulting integrands is proved before the
Bochner integral is split. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem integral_add_centered_constant {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F G : Ω→ℝ) (z : ℝ) (hF : Integrable F P)
    (hG : Integrable G P) (hzero : ∫p,G p ∂P=0) :
    Integrable (fun p=>F p+z*G p) P ∧
      (∫p,F p+z*G p ∂P)=∫p,F p ∂P :=by
  refine ⟨hF.add (hG.const_mul z),?_⟩
  rw [integral_add hF (hG.const_mul z),integral_const_mul,hzero,mul_zero,add_zero]

def cavityFixedRowOuterCenteredProduct (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (d : ℕ)
    (p : AnisotropicDisorder (n+1)×((Fin (k+2)→QuantitativePaper.Field (n+1))×Configuration (n+1))) : ℝ :=
  let R:=anisotropicRootEnergyMap D
  let W:=cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput D s) (k+2) d
  let f:=cavityFixedRowLastFieldSquare D s d
  let g:=cavityFixedRowRestFieldSquare D s d
  (f (0+R p.1+W p.2.1)-cavityOuterPosteriorMean (fun _ : Configuration (n+1)=>0)
      (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) a (k+2) R f W 0)*
    (g (0+R p.1+W p.2.1)-cavityOuterPosteriorMean (fun _ : Configuration (n+1)=>0)
      (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) a (k+2) R g W 0)

theorem integrable_cavityFixedRowOuterCenteredProduct (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (d : ℕ) :
    Integrable (cavityFixedRowOuterCenteredProduct D s a d)
      (cavityOuterPosteriorLaw (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s)
        (cavityFiniteEnergyInput D s) a (k+2) (anisotropicRootEnergyMap D) 0) :=by
  haveI:=cavityOuterPosteriorLaw_probability (fun _ : Configuration (n+1)=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) (cavityFiniteEnergyInput D s)
    a (k+2) (anisotropicRootEnergyMap D) 0
  let W:=cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput D s) (k+2) d
  have hf:=memLp_cavityOuterPosterior_fieldValue (fun _ : Configuration (n+1)=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) (cavityFiniteEnergyInput D s)
    a (k+2) (anisotropicRootEnergyMap D) (cavityFixedRowLastFieldSquare D s d)
    (boundedJets_cavityFixedRowLastFieldSquare D s d) W 0 (2:ENNReal)
  have hg:=memLp_cavityOuterPosterior_fieldValue (fun _ : Configuration (n+1)=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) (cavityFiniteEnergyInput D s)
    a (k+2) (anisotropicRootEnergyMap D) (cavityFixedRowRestFieldSquare D s d)
    (boundedJets_cavityFixedRowRestFieldSquare D s d) W 0 (2:ENNReal)
  exact (hf.sub (memLp_const _)).integrable_mul (hg.sub (memLp_const _))

theorem integral_cavityFixedRowOuterCenteredProduct_zero (s : RSBScheme k)
    (n : ℕ) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (a : ℝ) (d : ℕ) (hd : d≤k+2) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    (∫p,cavityFixedRowOuterCenteredProduct D s a d p
      ∂cavityOuterPosteriorLaw (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s)
        (cavityFiniteEnergyInput D s) a (k+2) (anisotropicRootEnergyMap D) 0)=0 :=by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
  have he:=cavityOuterPosteriorCovariance_eq_centeredMean (fun _ : Configuration (n+1)=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) (cavityFiniteEnergyInput D s)
    a (k+2) (anisotropicRootEnergyMap D) (cavityFixedRowLastFieldSquare D s d)
    (cavityFixedRowRestFieldSquare D s d) (boundedJets_cavityFixedRowLastFieldSquare D s d)
    (boundedJets_cavityFixedRowRestFieldSquare D s d)
    (cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput D s) (k+2) d)
    (cavityOuterPosteriorMean (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s)
      (cavityFiniteEnergyInput D s) a (k+2) (anisotropicRootEnergyMap D)
      (cavityFixedRowLastFieldSquare D s d)
      (cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput D s) (k+2) d) 0)
    (cavityOuterPosteriorMean (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s)
      (cavityFiniteEnergyInput D s) a (k+2) (anisotropicRootEnergyMap D)
      (cavityFixedRowRestFieldSquare D s d)
      (cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput D s) (k+2) d) 0) 0
  simp only [sub_self,zero_mul,sub_zero] at he
  change cavityOuterPosteriorMean (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s)
    (cavityFiniteEnergyInput D s) a (k+2) (anisotropicRootEnergyMap D)
    (fun Q=>(cavityFixedRowLastFieldSquare D s d Q-cavityOuterPosteriorMean
        (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s)
        a (k+2) (anisotropicRootEnergyMap D) (cavityFixedRowLastFieldSquare D s d)
        (cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput D s) (k+2) d) 0)*
      (cavityFixedRowRestFieldSquare D s d Q-cavityOuterPosteriorMean
        (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s)
        a (k+2) (anisotropicRootEnergyMap D) (cavityFixedRowRestFieldSquare D s d)
        (cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput D s) (k+2) d) 0))
    (cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput D s) (k+2) d) 0=0
  rw [←he]
  exact cavityFixedRowOuterCovariance_independent_zero s n β ρ hβ hρ a d hd

def cavityFixedRowOuterResponseWithoutNormalizer (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (d : ℕ) (i : Fin n)
    (p : AnisotropicDisorder (n+1)×((Fin (k+2)→QuantitativePaper.Field (n+1))×Configuration (n+1))) : ℝ :=
  cavityFixedRowOuterResponseIntegrand D s a d i p+
    exponentialDensityHessian (fun Q=>Real.log (cavityOuterPosteriorNormalizer
      (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s)
      a (k+2) (anisotropicRootEnergyMap D) Q)) 0
      (anisotropicPairFeature (followupCavityIncidentIndex i))
      (anisotropicPairFeature (followupCavityIncidentIndex i))*
        cavityFixedRowOuterCenteredProduct D s a d p

theorem cavityFixedRowOuterResponseWithoutNormalizer_integrable_eq (s : RSBScheme k)
    (n : ℕ) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (a : ℝ) (d : ℕ) (hd : d≤k+2) (i : Fin n) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    let P:=cavityOuterPosteriorLaw (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s)
      (cavityFiniteEnergyInput D s) a (k+2) (anisotropicRootEnergyMap D) 0
    Integrable (cavityFixedRowOuterResponseWithoutNormalizer D s a d i) P ∧
      (∫p,cavityFixedRowOuterResponseWithoutNormalizer D s a d i p ∂P)=
        ∫p,cavityFixedRowOuterResponseIntegrand D s a d i p ∂P :=by
  dsimp only
  apply integral_add_centered_constant
  · exact integrable_cavityOuterPosterior_responseIntegrand _ _ (anisotropicSchemeMass_nonneg s)
      (anisotropicSchemeMass_le_one s 0)
      (antitone_nat_of_succ_le (anisotropicSchemeMass_antitone_step s)) _ a (k+2) _ _ _
      (boundedJets_cavityFixedRowLastFieldSquare _ s d)
      (boundedJets_cavityFixedRowRestFieldSquare _ s d) _ 0 _ _ _
  · exact integrable_cavityFixedRowOuterCenteredProduct _ s a d
  · exact integral_cavityFixedRowOuterCenteredProduct_zero s n β ρ hβ hρ a d hd

end QuantitativeFollowup
