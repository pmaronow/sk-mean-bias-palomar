module
public import QuantitativeFollowup.StandardSKPosteriorVariance
public import QuantitativeFollowup.StandardSKPrintedCoefficients
public import QuantitativeFollowup.FoundationJointMartingale
public import QuantitativePaper.VectorMeasureMatrixOrder
public import QuantitativePaper.VectorPhysicalFutureConditionalLaw

@[expose] public section

/-! The printed standard SK specialization of follow-up Lemma 2.2, on its
actual completed Gaussian disorder and marked diffusion law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
namespace QuantitativeFollowup
open QuantitativePaper FourPapersCommon
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

structure StandardSKPosteriorTarget (n : ℕ) (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t<1) : Prop where
  gradient : ∀ (q : Paper.Overlap) (p : Couplings n×ℝ) (x w : Field n),
    fderiv ℝ (vectorMeasureTailPotential μ β t q p) x w=inner ℝ (vectorMeasureGradient μ β t q p x) w
  conditional_mean : ∀q : Paper.Overlap,
    (vectorMeasureSpinPathLaw (n:=n) μ β t a ht.le)[
      (fun p : VectorDisorderBrownianSample n×Configuration n=>spinVector p.2)|foundationSpinFiltration n q]
      =ᵐ[vectorMeasureSpinPathLaw μ β t a ht.le] fun p=>vectorMeasureSpinMean μ β t ht.le q p.1
  initial_zero : ∀sample : VectorDisorderBrownianSample n,vectorMeasureSpinMean μ β t ht.le 0 sample=0
  martingale : Martingale (fun q : Paper.Overlap=>fun p : VectorDisorderBrownianSample n×Configuration n=>
    vectorMeasureSpinMean μ β t ht.le q p.1) (foundationSpinFiltration n) (vectorMeasureSpinPathLaw μ β t a ht.le)
  conditional_covariance : ∀q : Paper.Overlap,
    ∀ᵐp ∂vectorMeasureSpinPathLaw (n:=n) μ β t a ht.le,
      vectorPhysicalSpinCovariance μ β t a ht.le q p=vectorMeasureSpinCovariance μ β t a ht.le q p.1
  covariance_order : ∀q : Paper.Overlap,
    ∀ᵐp ∂vectorMeasureSpinPathLaw (n:=n) μ β t a ht.le,
      (vectorMeasureSpinCovariance μ β t a ht.le q p.1).PosSemidef ∧
      (vectorMeasureHessianMatrix μ β t ht.le q p.1-
        Paper.parisiCDF μ q • vectorMeasureSpinCovariance μ β t a ht.le q p.1).PosSemidef ∧
      (vectorMeasureSpinCovariance μ β t a ht.le q p.1-vectorMeasureHessianMatrix μ β t ht.le q p.1).PosSemidef
  signed_variance : ∀ (κ : Paper.Overlap→ℝ),MemLp κ 2 (parisiFreeMeasure μ a)→
    ∀ (J : Finset (Fin n)),J.Nonempty→
    variance (fun p : VectorDisorderBrownianSample n×Configuration n=>standardSKWeightedSelfOverlap μ β t a ht.le κ J p.1)
      (vectorMeasureSpinPathLaw μ β t a ht.le) ≤
      (4/(J.card:ℝ)^2)*(∫q,(κ q)^2*(∫sample,standardSKSelectedHessianEnergy μ β t ht.le J q sample
        ∂vectorMeasureDisorderTilt μ β t a) ∂parisiFreeMeasure μ a) ∧
    ((4/(J.card:ℝ)^2)*(∫q,(κ q)^2*(∫sample,standardSKSelectedHessianEnergy μ β t ht.le J q sample
      ∂vectorMeasureDisorderTilt μ β t a) ∂parisiFreeMeasure μ a)) ≤
      (4/(J.card:ℝ)^2)*(∫q,(κ q)^2*(∫sample,standardSKSelectedCovarianceEnergy μ β t a ht.le J q sample
        ∂vectorMeasureDisorderTilt μ β t a) ∂parisiFreeMeasure μ a)
  energy_integrability : ∀ (κ : Paper.Overlap→ℝ),MemLp κ 2 (parisiFreeMeasure μ a)→
    ∀ (J : Finset (Fin n)),
    Integrable (fun q=>(κ q)^2*(∫sample,standardSKSelectedHessianEnergy μ β t ht.le J q sample
      ∂vectorMeasureDisorderTilt μ β t a)) (parisiFreeMeasure μ a) ∧
    Integrable (fun q=>(κ q)^2*(∫sample,standardSKSelectedCovarianceEnergy μ β t a ht.le J q sample
      ∂vectorMeasureDisorderTilt μ β t a)) (parisiFreeMeasure μ a)

theorem standardSK_posterior_self_overlap (hn : 0<n) (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) :
    StandardSKPosteriorTarget n μ β t a ht where
  gradient := fun q p x w=>by
    rw [(hasFDerivAt_vectorMeasureTailPotential μ β t ht.le q p x).fderiv]
    rfl
  conditional_mean := foundation_terminal_spin_condExp μ β t a hβ ht
  initial_zero := vectorMeasureSpinMean_zero μ β t ht.le
  martingale := foundation_joint_spin_mean_martingale μ β t a hβ ht
  conditional_covariance := vectorPhysicalSpinCovariance_eq_base μ β t a ht.le
  covariance_order := fun q=>(measurePreserving_vectorMeasureSpinPathLaw_fst μ β t a ht.le).quasiMeasurePreserving.ae
    (vectorMeasure_matrix_order μ β t a hβ ht q)
  signed_variance := fun κ hL J hJ=>standardSK_marked_selfOverlap_variance hn μ β t a hβ ht ha hμ κ hL J hJ
  energy_integrability := fun κ hL J=>integrable_standardSKWeightedEnergyBudgets μ β t a hβ ht J κ hL

/-- Both models in the printed lemma, with the actual standard marked-law transport. -/
theorem followup_posterior_self_overlap_both_models (hn : 0<n) (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) :
    StandardSKPosteriorTarget n μ β t a ht ∧
    (∀D : AnisotropicSpinModel n,AnisotropicPosteriorTarget D μ a) ∧
    (anisotropicMeasureSpinPathLaw (standardSKAnisotropicModel n β t hβ ht) μ a).map
      standardSKMarkedCompression=vectorMeasureSpinPathLaw μ β t a ht.le :=
  ⟨standardSK_posterior_self_overlap hn μ β t a hβ ht ha hμ,
    fun D=>anisotropic_posterior_self_overlap D μ a ha hμ,
    standardSKAnisotropicMarkedLaw hn μ β t a hβ ht⟩

end QuantitativeFollowup
