module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseRowJets
public import QuantitativeFollowup.FollowupCavityCppZeroResponseLastVarianceFieldExpectation
public import QuantitativeFollowup.FollowupCavityFixedRowLineMarginal
public import QuantitativeFollowup.FixedRowSymmetryPosteriorTransportDensity
public import QuantitativeFollowup.FollowupCavityCppZeroResponsePosteriorObservableJets

@[expose] public section

/-! The future-square factors in the pointwise zero-row Hessian identity
are genuine smooth continuation expectations. The normalized posterior is
transported to the retained line before any spatial differentiation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped ContDiff
namespace QuantitativeFollowup
open SpinGlass.Targets SpinGlass.AT OverlapPaper FiniteTerminalGenealogy
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

variable {S : Type} [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n k : ℕ}

theorem cavityRowSecondSpatial_futureEnergy_eq_posterior
    (V : S → ℝ) (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (L : ℕ → Field n →L[ℝ] FiniteStateField S) (p j : ℕ)
    (f : FiniteStateField S → ℝ) (hf : BoundedJets f) (H : FiniteStateField S) :
    sourceKernelExpectation
      (fun r => finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (p+r)) j f H =
      cavityPosteriorTranslatedMean V a L (p+j) f
        (fun z => cavityPosteriorLineFieldLinear L (p+j) p z.1) H := by
  have hmeas := hf.1.continuous.measurable
  obtain ⟨C, hC, hb⟩ := hf.2 0
  have hbound : ∀ Q, |f Q| ≤ C := fun Q => by
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hb Q
  have hpj : p ≤ p+j := Nat.le_add_right _ _
  have hline := integral_cavityFixedRowLineField_eq_sourceKernelExpectation
    V a ha L (p+j) p hpj H f hmeas C hbound
  rw [Nat.add_sub_cancel_left] at hline
  rw [←hline, ←cavityPosteriorGaussianLaw_map_lineRecord V a ha L (p+j) H]
  have hm : Measurable (cavityPosteriorLineRecord L (p+j) H) :=
    (measurable_cavityPosteriorLineRecord L (p+j)).comp
      (measurable_const.prodMk measurable_id)
  have ho : Measurable (fun z => f (cavityFixedRowLineField (p+j) p H z)) :=
    hmeas.comp ((measurable_cavityFixedRowLineField_marginal
      (E:=FiniteStateField S) (S:=S) (p+j) p).comp
        (measurable_const.prodMk measurable_id))
  rw [integral_map hm.aemeasurable ho.aestronglyMeasurable]
  simp only [cavityPosteriorLineRecord_field_affine L (p+j) p hpj,
    cavityPosteriorTranslatedMean]

theorem contDiff_cavityRowSecondSpatial_futureEnergy
    (V : S → ℝ) (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (ha1 : a 0 ≤ 1) (hdec : Antitone a)
    (L : ℕ → Field n →L[ℝ] FiniteStateField S) (p j : ℕ)
    (f : FiniteStateField S → ℝ) (hf : BoundedJets f) :
    ContDiff ℝ ∞ (sourceKernelExpectation
      (fun r => finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (p+r)) j f) := by
  have he : sourceKernelExpectation
      (fun r => finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (p+r)) j f =
      cavityPosteriorTranslatedMean V a L (p+j) f
        (fun z => cavityPosteriorLineFieldLinear L (p+j) p z.1) :=
    funext (cavityRowSecondSpatial_futureEnergy_eq_posterior V a ha L p j f hf)
  rw [he]
  exact (boundedJets_cavityPosteriorTranslatedMean V a ha ha1 hdec L (p+j) f hf
    (cavityPosteriorLineFieldLinear L (p+j) p)).1

theorem contDiff_cavityFiniteRowFutureRestSquare (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1) (p j : ℕ) (i : Fin n) :
    ContDiff ℝ ∞ (cavityFiniteRowFutureRestSquare s n β ρ hβ hρ p j i) := by
  let D := followupCavityRestSpinModel n β ρ hβ hρ
  let b : FiniteStateField (QuantitativePaper.Configuration n) :=
    WithLp.toLp 2 (fun σ : QuantitativePaper.Configuration n => Paper.spinSign (σ i))
  let f : FiniteStateField (QuantitativePaper.Configuration n) → ℝ := fun H =>
    (cavityFiniteEnergyFeatureMean (fun _ : QuantitativePaper.Configuration n => 0)
      (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) p b H)^2
  have hf : BoundedJets f := by
    have hb := boundedJets_cavityFiniteEnergyFeatureMean (fun _ : QuantitativePaper.Configuration n => 0)
      (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
      (cavityFiniteEnergyInput D s) p b
    simpa only [f, pow_two] using hb.mul hb
  have he : cavityFiniteRowFutureRestSquare s n β ρ hβ hρ p j i =
      (sourceKernelExpectation (fun r => finiteStateGaussianCascadeKernel
        (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s)
        (gtStateLogPartition (fun _ : QuantitativePaper.Configuration n => 0)) (p+r)) j f) ∘
          anisotropicEnergyMap D := by
    funext P
    have ht := cavityFiniteEnergyExpectation_at_parameter D s p j f
      hf.1.continuous.measurable P
    simp only [f, b, cavityFiniteEnergyFeatureMean_at_parameter] at ht
    exact ht.symm
  rw [he]
  exact (contDiff_cavityRowSecondSpatial_futureEnergy _ _ (anisotropicSchemeMass_nonneg s)
    (anisotropicSchemeMass_le_one s 0)
    (antitone_nat_of_succ_le (anisotropicSchemeMass_antitone_step s))
    (cavityFiniteEnergyInput D s) p j f hf).comp (anisotropicEnergyMap D).contDiff

theorem contDiff_cavityFiniteRowFutureScalarSquare (s : RSBScheme k) (β : ℝ)
    (hβ : 0 < β) (p j : ℕ) :
    ContDiff ℝ ∞ (cavityFiniteRowFutureScalarSquare s β p j) := by
  have hb : 0 < β^2 := sq_pos_of_pos hβ
  let D := cavityLastVarianceModel 0 1 1 (by norm_num) (by norm_num) (β^2) hb
  let E : ℝ →L[ℝ] AnisotropicParameter 1 :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (anisotropicCoordinateDirection 1 (Fin.last 0))
  let f := cavityFixedRowLastFieldSquare D s p
  have hf : BoundedJets f := boundedJets_cavityFixedRowLastFieldSquare D s p
  have he : cavityFiniteRowFutureScalarSquare s β p j =
      (sourceKernelExpectation (fun r => finiteStateGaussianCascadeKernel
        (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s)
        (gtStateLogPartition (fun _ : QuantitativePaper.Configuration 1 => 0)) (p+r)) j f) ∘
          ((anisotropicEnergyMap D).comp E) := by
    funext x
    have hlast : E x (Sum.inr (Fin.last 0)) = x := by
      simp [E, anisotropicCoordinateDirection, anisotropicFieldInjection,
        EuclideanSpace.single_apply]
    have ht := cavityLastVariance_energy_last_mean s 0 1 1
      (by norm_num) (by norm_num) (β^2) hb p j (E x)
    dsimp only [cavityLastVarianceScalarSquareMean] at ht
    rw [Real.sqrt_sq hβ.le, hlast] at ht
    exact ht.symm
  rw [he]
  exact (contDiff_cavityRowSecondSpatial_futureEnergy _ _ (anisotropicSchemeMass_nonneg s)
    (anisotropicSchemeMass_le_one s 0)
    (antitone_nat_of_succ_le (anisotropicSchemeMass_antitone_step s))
    (cavityFiniteEnergyInput D s) p j f hf).comp ((anisotropicEnergyMap D).comp E).contDiff

end QuantitativeFollowup
