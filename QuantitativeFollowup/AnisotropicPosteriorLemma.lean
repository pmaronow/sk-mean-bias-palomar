module
public import QuantitativeFollowup.AnisotropicVarianceLiteral
public import QuantitativeFollowup.AnisotropicSpinMartingale
public import QuantitativeFollowup.AnisotropicCovarianceComparison

@[expose] public section

/-! The full-profile generalized-law assertion of follow-up Lemma 2.2.
The model is the literal independent Gaussian coupling model with arbitrary
real coupling scales and positive diagonal auxiliary covariance. Its law,
state, terminal spin, Hessian and conditional covariance are the constructed
objects; every assertion below is proved without posterior-law or stochastic
identification assumptions. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators NNReal
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128

theorem anisotropicMeasureTailMagnetization_apply (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n) (i : Fin n) :
    anisotropicMeasureTailMagnetization D μ q P i=
      fderiv ℝ (anisotropicMeasureTailPotential D μ q) P (anisotropicCoordinateDirection n i) := rfl

/-- Literal conclusions of Lemma 2.2 for the actual generalized law. -/
structure AnisotropicPosteriorTarget (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) : Prop where
  gradient : ∀ q P w,
    fderiv ℝ (anisotropicMeasureTailPotential D μ q) P (anisotropicFieldInjection n w)=
      inner ℝ (anisotropicMeasureTailMagnetization D μ q P) w
  conditional_mean : ∀ q : Paper.Overlap,
    (anisotropicMeasureSpinPathLaw D μ a)[
      (fun p : AnisotropicDisorderBrownianSample n×Configuration n=>spinVector p.2)|
        anisotropicSpinFiltration n q]=ᵐ[anisotropicMeasureSpinPathLaw D μ a]
      fun p=>anisotropicProcessMagnetization D μ q p.1
  initial_zero : ∀ sample, anisotropicProcessMagnetization D μ 0 sample=0
  martingale : Martingale (fun q : Paper.Overlap=>fun p :
      AnisotropicDisorderBrownianSample n×Configuration n=>
      anisotropicProcessMagnetization D μ q p.1)
    (anisotropicSpinFiltration n) (anisotropicMeasureSpinPathLaw D μ a)
  conditional_covariance : ∀ (q : Paper.Overlap) (i j : Fin n),
    (fun p : AnisotropicDisorderBrownianSample n×Configuration n=>
      (anisotropicMeasureSpinPathLaw D μ a)[
        (fun z : AnisotropicDisorderBrownianSample n×Configuration n=>
          Paper.spinSign (z.2 i)*Paper.spinSign (z.2 j))|
          anisotropicSpinPast n (q:ℝ).toNNReal] p-
      (anisotropicMeasureSpinPathLaw D μ a)[
        (fun z : AnisotropicDisorderBrownianSample n×Configuration n=>Paper.spinSign (z.2 i))|
          anisotropicSpinPast n (q:ℝ).toNNReal] p*
      (anisotropicMeasureSpinPathLaw D μ a)[
        (fun z : AnisotropicDisorderBrownianSample n×Configuration n=>Paper.spinSign (z.2 j))|
          anisotropicSpinPast n (q:ℝ).toNNReal] p)=ᵐ[anisotropicMeasureSpinPathLaw D μ a]
      fun p=>anisotropicProcessSpinCovariance D μ q p.1 i j
  covariance_order : ∀ (q : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) (w : Field n),
    Paper.parisiCDF μ q*anisotropicTailCovarianceQuadratic D μ q
      (anisotropicProcessParameter D μ q sample) w ≤
      fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ q))
        (anisotropicProcessParameter D μ q sample)
        (anisotropicFieldInjection n w) (anisotropicFieldInjection n w) ∧
    fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ q))
        (anisotropicProcessParameter D μ q sample)
        (anisotropicFieldInjection n w) (anisotropicFieldInjection n w) ≤
      anisotropicTailCovarianceQuadratic D μ q (anisotropicProcessParameter D μ q sample) w
  signed_variance : ∀ (κ : Paper.Overlap→ℝ), MemLp κ 2 (parisiFreeMeasure μ a)→
    ∀ (J : Finset (Fin n)), J.Nonempty→
    variance (fun p : AnisotropicDisorderBrownianSample n×Configuration n=>
        anisotropicWeightedSelfOverlap D μ a κ J p.1) (anisotropicMeasureSpinPathLaw D μ a) ≤
      (4/(J.card:ℝ)^2)*(∫q,(κ q)^2*(∫p : AnisotropicDisorderBrownianSample n×Configuration n,
        anisotropicProcessHessianEnergy D μ J q p.1 ∂anisotropicMeasureSpinPathLaw D μ a)
        ∂parisiFreeMeasure μ a) ∧
    ((4/(J.card:ℝ)^2)*(∫q,(κ q)^2*(∫p : AnisotropicDisorderBrownianSample n×Configuration n,
        anisotropicProcessHessianEnergy D μ J q p.1 ∂anisotropicMeasureSpinPathLaw D μ a)
        ∂parisiFreeMeasure μ a)) ≤
      (4/(J.card:ℝ)^2)*(∫q,(κ q)^2*(∫p : AnisotropicDisorderBrownianSample n×Configuration n,
        anisotropicProcessCovarianceEnergy D μ J q p.1 ∂anisotropicMeasureSpinPathLaw D μ a)
        ∂parisiFreeMeasure μ a)

theorem anisotropic_posterior_self_overlap (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) :
    AnisotropicPosteriorTarget D μ a where
  gradient := fderiv_anisotropicMeasureTailPotential_field D μ
  conditional_mean := anisotropic_terminal_spin_condExp D μ a
  initial_zero := anisotropicProcessMagnetization_zero D μ
  martingale := anisotropic_joint_spin_mean_martingale D μ a
  conditional_covariance := anisotropicProcessSpinCovariance_eq_conditional D μ a
  covariance_order := fun q sample w=>anisotropicMeasureTail_covariance_bounds D μ q
    (anisotropicProcessParameter D μ q sample) w
  signed_variance := fun κ hL J hJ=>anisotropic_marked_selfOverlap_variance_literal D μ a ha hμ κ hL J hJ

end QuantitativeFollowup
