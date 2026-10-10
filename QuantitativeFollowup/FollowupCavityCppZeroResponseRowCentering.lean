module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseRowPullback
public import QuantitativeFollowup.FollowupCavityCppZeroResponseLastVarianceCovariance
public import QuantitativeFollowup.FollowupCavityFixedRowSymmetry

@[expose] public section

/-! Actual centering at the independent endpoint. Reflection makes both
retained mean gradients zero in every incident direction; the isolated
last-spin product law makes the centered covariance zero as well. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped ContDiff
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem first_comp_linear_zero {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F→ℝ) (hf : DifferentiableAt ℝ f 0) (B : E→L[ℝ]F) (e : E) :
    fderiv ℝ (f ∘ B) 0 e=fderiv ℝ f 0 (B e) :=by
  rw [fderiv_comp (0:E) (by simpa only [map_zero] using hf) B.differentiableAt,
    ContinuousLinearMap.fderiv,ContinuousLinearMap.comp_apply,map_zero]

private theorem outer_mean_zero_of_recorded_zero (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (d : ℕ) (hd : d≤k+2)
    (f : FiniteStateField (QuantitativePaper.Configuration (n+1))→ℝ) (hf : BoundedJets f)
    (hzero : fderiv ℝ (cavityFixedRowFieldMean D s a d f) 0=0) (i : Fin n) :
    fderiv ℝ (cavityOuterPosteriorMean (fun _ : QuantitativePaper.Configuration (n+1)=>0)
      (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) a (k+2)
      (anisotropicRootEnergyMap D) f (cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput D s) (k+2) d))
      0 (anisotropicPairFeature (followupCavityIncidentIndex i))=0 :=by
  let M:=cavityOuterPosteriorMean (fun _ : QuantitativePaper.Configuration (n+1)=>0)
    (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) a (k+2)
    (anisotropicRootEnergyMap D) f (cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput D s) (k+2) d)
  have he : cavityFixedRowFieldMean D s a d f=M ∘ cavityFixedRowOffset n:=by
    exact cavityFixedRowFieldMean_eq_outer D s a d hd f hf.1.continuous.measurable
  have hM : DifferentiableAt ℝ M 0:=
    (contDiff_cavityOuterPosteriorMean _ _ (anisotropicSchemeMass_nonneg s)
      (anisotropicSchemeMass_le_one s 0)
      (antitone_nat_of_succ_le (anisotropicSchemeMass_antitone_step s)) _ a (k+2) _ f hf _).differentiable (by simp) _
  have hz:=congrArg (fun T : Field n→L[ℝ]ℝ=>T (EuclideanSpace.basisFun (Fin n) ℝ i)) hzero
  rw [he,first_comp_linear_zero M hM,cavityFixedRowOffset_basis] at hz
  exact hz

theorem cavityFixedRowOuter_last_mean_first_zero (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (d : ℕ) (hd : d≤k+2) (i : Fin n) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    fderiv ℝ (cavityOuterPosteriorMean (fun _ : QuantitativePaper.Configuration (n+1)=>0)
      (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) a (k+2)
      (anisotropicRootEnergyMap D) (cavityFixedRowLastFieldSquare D s d)
      (cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput D s) (k+2) d))
      0 (anisotropicPairFeature (followupCavityIncidentIndex i))=0 :=by
  dsimp only
  exact outer_mean_zero_of_recorded_zero _ s a d hd _ (boundedJets_cavityFixedRowLastFieldSquare _ s d)
    (fderiv_cavityFixedRowLastSquare_integral_zero β ρ hβ hρ s a d) i

theorem cavityFixedRowOuter_rest_mean_first_zero (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (d : ℕ) (hd : d≤k+2) (i : Fin n) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    fderiv ℝ (cavityOuterPosteriorMean (fun _ : QuantitativePaper.Configuration (n+1)=>0)
      (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) a (k+2)
      (anisotropicRootEnergyMap D) (cavityFixedRowRestFieldSquare D s d)
      (cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput D s) (k+2) d))
      0 (anisotropicPairFeature (followupCavityIncidentIndex i))=0 :=by
  dsimp only
  exact outer_mean_zero_of_recorded_zero _ s a d hd _ (boundedJets_cavityFixedRowRestFieldSquare _ s d)
    (fderiv_cavityFixedRowRestSquare_integral_zero β ρ hβ hρ s a d) i

theorem cavityFixedRowOuter_logNormalizer_first_zero (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (i : Fin n) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    fderiv ℝ (fun Q=>Real.log (cavityOuterPosteriorNormalizer
      (fun _ : QuantitativePaper.Configuration (n+1)=>0) (anisotropicSchemeMass s)
      (cavityFiniteEnergyInput D s) a (k+2) (anisotropicRootEnergyMap D) Q))
      0 (anisotropicPairFeature (followupCavityIncidentIndex i))=0 :=by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
  let Z:=cavityOuterPosteriorNormalizer (fun _ : QuantitativePaper.Configuration (n+1)=>0)
    (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) a (k+2) (anisotropicRootEnergyMap D)
  have hZ : DifferentiableAt ℝ Z 0:=
    (contDiff_cavityOuterPosteriorNormalizer _ _ (anisotropicSchemeMass_nonneg s) _ a (k+2) _).differentiable (by simp) _
  have he : cavityFixedRowNormalizer D s a=Z ∘ cavityFixedRowOffset n:=rfl
  have hz:=congrArg (fun T : Field n→L[ℝ]ℝ=>T (EuclideanSpace.basisFun (Fin n) ℝ i))
    (fderiv_cavityFixedRowNormalizer_zero β ρ hβ hρ s a)
  rw [he,first_comp_linear_zero Z hZ,cavityFixedRowOffset_basis] at hz
  have hlog:=(hZ.hasFDerivAt.log (finiteCascadeTreeGaussianNormalizer_pos _ _ (anisotropicSchemeMass_nonneg s)
    _ a (k+2) _ 0).ne').fderiv
  rw [hlog,ContinuousLinearMap.smul_apply,hz]
  simp only [ContinuousLinearMap.zero_apply,smul_zero]

end QuantitativeFollowup
