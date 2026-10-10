module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeHistoryMoments
public import QuantitativeFollowup.FollowupCavityFixedRowNativeFieldSquares
public import QuantitativeFollowup.FollowupCavityFourRestVarianceComparison
public import QuantitativeFollowup.ScalarFutureSquare
public import QuantitativeFollowup.FollowupCavitySignedResponseSelfOverlap

@[expose] public section

/-! The actual outer centering constants are the native scalar Gamma and
rest overlap mean. Their complete-law transport preserves the terminal
mark and the original retained observation, including repeated levels. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem cavityScalarMagnetization_eq_M (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (ω : Paper.BrownianSample) :
    cavityScalarMagnetization β hβ μ q ω=FRSB.M β μ q ω :=by
  unfold cavityScalarMagnetization
  rw [←parisiPhysicalSplitState_eq_selected β hβ μ q ω]
  exact scalarGradient_physicalSplitState β hβ μ q ω

theorem integral_cavityLastProcessSquare_zero (μ : Paper.ParisiMeasure) (n : ℕ)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (q : Paper.Overlap) :
    (∫sample,(anisotropicProcessSpinResponse
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ q
      (Fin.last n) sample)^2 ∂anisotropicMeasureSampleLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a)=
      FRSB.Gamma (followupCavityScalarBeta n β ρ) μ q :=by
  let B:=followupCavityScalarBeta n β ρ
  have hs : HasLaw Prod.snd Paper.canonicalBrownianMeasure
      ((anisotropicMeasureSampleLaw (followupCavityRestSpinModel n β ρ hβ hρ) μ a).prod
        Paper.canonicalBrownianMeasure):=
    ⟨measurable_snd.aemeasurable,measurePreserving_snd.map_eq⟩
  have hl:=hs.comp (hasLaw_cavityZeroSampleSplit μ n β ρ hβ hρ a)
  have hm : AEStronglyMeasurable (fun ω => (FRSB.M B μ q ω)^2) Paper.canonicalBrownianMeasure :=
    ((FRSB.measurable_M B μ q q.property).pow_const 2).aestronglyMeasurable
  have he:=hl.integral_comp hm
  simp_rw [anisotropicProcessSpinResponse,cavityLastProcessMagnetization_zero,
    cavityScalarMagnetization_eq_M]
  simpa only [Function.comp_def,cavityZeroSampleSplit,FRSB.Gamma,B] using he

theorem integral_cavityRestProcessSquare_zero (μ : Paper.ParisiMeasure) (n : ℕ)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (q : Paper.Overlap) :
    (∫sample,anisotropicSelectedMeanSquare (Finset.univ.erase (Fin.last n))
      (anisotropicProcessMagnetization
        (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ q sample)
      ∂anisotropicMeasureSampleLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a)=
      cavityRestOverlapMean (followupCavityRestSpinModel n β ρ hβ hρ) μ a q :=by
  simp_rw [cavityRestSelectedMeanSquare_zero]
  rw [cavityRestOverlapMean_apply]
  exact (hasLaw_cavityRestSampleProjection μ n β ρ hβ hρ a).integral_comp
    (measurable_cavityRestSelfOverlap _ μ q).aestronglyMeasurable

theorem cavityFixedRowOuterLastMean_zero_eq_Gamma (s : RSBScheme k) (n : ℕ)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (d : ℕ) (hd : d≤k+2) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    cavityOuterPosteriorMean (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s)
      (cavityFiniteEnergyInput D s) a (k+2) (anisotropicRootEnergyMap D)
      (cavityFixedRowLastFieldSquare D s d)
      (cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput D s) (k+2) d) 0=
      FRSB.Gamma (followupCavityScalarBeta n β ρ) (Paper.parisiSchemeMeasure s)
        (anisotropicSchemeNode s (k+2-d) (by omega)) :=by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
  let q:=anisotropicSchemeNode s (k+2-d) (by omega)
  rw [cavityOuterPosteriorMean_eq_native_scheme_node D s a d hd _
    (boundedJets_cavityFixedRowLastFieldSquare D s d).1.continuous.measurable]
  simp_rw [cavityFixedRowLastFieldSquare_at_native_scheme_node D s d hd]
  rw [integral_anisotropicMeasureSpinPathLaw_sample D (Paper.parisiSchemeMeasure s) a _
    ((measurable_anisotropicProcessSpinResponse D (Paper.parisiSchemeMeasure s) q (Fin.last n)).pow_const 2)]
  exact integral_cavityLastProcessSquare_zero (Paper.parisiSchemeMeasure s) n β ρ hβ hρ a q

private theorem cavityFixedRowOuterRestMean_eq_native_selected
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (d : ℕ) (hd : d≤k+2) :
    cavityOuterPosteriorMean (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s)
      (cavityFiniteEnergyInput D s) a (k+2) (anisotropicRootEnergyMap D)
      (cavityFixedRowRestFieldSquare D s d)
      (cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput D s) (k+2) d) 0=
      ∫sample,anisotropicSelectedMeanSquare (Finset.univ.erase (Fin.last n))
        (anisotropicProcessMagnetization D (Paper.parisiSchemeMeasure s)
          (anisotropicSchemeNode s (k+2-d) (by omega)) sample)
        ∂anisotropicMeasureSampleLaw D (Paper.parisiSchemeMeasure s) a :=by
  let q:=anisotropicSchemeNode s (k+2-d) (by omega)
  let F : AnisotropicDisorderBrownianSample (n+1) → ℝ := fun sample =>
    anisotropicSelectedMeanSquare (Finset.univ.erase (Fin.last n))
      (anisotropicProcessMagnetization D (Paper.parisiSchemeMeasure s) q sample)
  have hM : Measurable (fun sample : AnisotropicDisorderBrownianSample (n+1) =>
      anisotropicProcessMagnetization D (Paper.parisiSchemeMeasure s) q sample) :=
    (adapted_anisotropicProcessMagnetization D (Paper.parisiSchemeMeasure s) q).mono
      ((anisotropicBrownianFiltration (n+1)).le _) le_rfl
  have hF : Measurable F :=
    (continuous_anisotropicSelectedMeanSquare _).measurable.comp hM
  have htransport := cavityOuterPosteriorMean_eq_native_scheme_node D s a d hd
    (cavityFixedRowRestFieldSquare D s d)
    (boundedJets_cavityFixedRowRestFieldSquare D s d).1.continuous.measurable
  have hp : (∫z,cavityFixedRowRestFieldSquare D s d
      (anisotropicEnergyMap D (anisotropicProcessParameter D (Paper.parisiSchemeMeasure s) q z.1))
      ∂anisotropicMeasureSpinPathLaw D (Paper.parisiSchemeMeasure s) a)=
      ∫z,F z.1 ∂anisotropicMeasureSpinPathLaw D (Paper.parisiSchemeMeasure s) a :=by
    apply integral_congr_ae
    exact .of_forall fun z=>cavityFixedRowRestFieldSquare_at_native_scheme_node D s d hd z.1
  exact htransport.trans (hp.trans (integral_anisotropicMeasureSpinPathLaw_sample D
    (Paper.parisiSchemeMeasure s) a F hF))

theorem cavityFixedRowOuterRestMean_zero_eq_mean (s : RSBScheme k) (n : ℕ)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (d : ℕ) (hd : d≤k+2) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    cavityOuterPosteriorMean (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s)
      (cavityFiniteEnergyInput D s) a (k+2) (anisotropicRootEnergyMap D)
      (cavityFixedRowRestFieldSquare D s d)
      (cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput D s) (k+2) d) 0=
      cavityRestOverlapMean (followupCavityRestSpinModel n β ρ hβ hρ)
        (Paper.parisiSchemeMeasure s) a (anisotropicSchemeNode s (k+2-d) (by omega)) :=by
  dsimp only
  exact (cavityFixedRowOuterRestMean_eq_native_selected
    (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) s a d hd).trans
    (integral_cavityRestProcessSquare_zero (Paper.parisiSchemeMeasure s) n β ρ hβ hρ a
      (anisotropicSchemeNode s (k+2-d) (by omega)))

theorem cavityFixedRowNativeLastCentered_zero (s : RSBScheme k) (n : ℕ)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (d : ℕ) (hd : d≤k+2)
    (sample : AnisotropicDisorderBrownianSample (n+1)) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    let q:=anisotropicSchemeNode s (k+2-d) (by omega)
    cavityFixedRowLastFieldSquare D s d
      (anisotropicEnergyMap D (anisotropicProcessParameter D (Paper.parisiSchemeMeasure s) q sample))-
      cavityOuterPosteriorMean (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s)
        (cavityFiniteEnergyInput D s) a (k+2) (anisotropicRootEnergyMap D)
        (cavityFixedRowLastFieldSquare D s d)
        (cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput D s) (k+2) d) 0=
      scalarCenteredSquare (followupCavityScalarBeta n β ρ) (Paper.parisiSchemeMeasure s) q
        (sample.2 (Fin.last n)) :=by
  dsimp only
  rw [cavityFixedRowLastFieldSquare_at_native_scheme_node _ s d hd,
    cavityFixedRowOuterLastMean_zero_eq_Gamma s n β ρ hβ hρ a d hd]
  simp only [anisotropicProcessSpinResponse,cavityLastProcessMagnetization_zero,
    cavityScalarMagnetization_eq_M,scalarCenteredSquare]

theorem cavityFixedRowNativeRestCentered_zero (s : RSBScheme k) (n : ℕ)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (d : ℕ) (hd : d≤k+2)
    (sample : AnisotropicDisorderBrownianSample (n+1)) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    let q:=anisotropicSchemeNode s (k+2-d) (by omega)
    cavityFixedRowRestFieldSquare D s d
      (anisotropicEnergyMap D (anisotropicProcessParameter D (Paper.parisiSchemeMeasure s) q sample))-
      cavityOuterPosteriorMean (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s)
        (cavityFiniteEnergyInput D s) a (k+2) (anisotropicRootEnergyMap D)
        (cavityFixedRowRestFieldSquare D s d)
        (cavityPosteriorLineFieldLinear (cavityFiniteEnergyInput D s) (k+2) d) 0=
      cavitySignedResponseCenteredSelfOverlap (followupCavityRestSpinModel n β ρ hβ hρ)
        (Paper.parisiSchemeMeasure s) a q (cavityRestSampleProjection n sample) :=by
  dsimp only
  rw [cavityFixedRowRestFieldSquare_at_native_scheme_node _ s d hd,
    cavityRestSelectedMeanSquare_zero,cavityFixedRowOuterRestMean_zero_eq_mean s n β ρ hβ hρ a d hd]
  rw [cavitySignedResponseCenteredSelfOverlap,cavityRestOverlapMean_apply]
  rfl

end QuantitativeFollowup
