module
public import QuantitativeFollowup.AnisotropicVarianceResponseLimit
public import FourPapersCommon.MovingDerivativeLimit

@[expose] public section

/-! Actual diagonal-variance differentiation of the arbitrary-profile
potential, obtained from genuine finite Gaussian derivatives and their
moving-parameter Stieltjes limit. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem hasDerivAt_anisotropicMeasureTailPotential_variance_restart
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (i : Fin n)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) (b : ℝ) (hb : 0<b) :
    HasDerivAt (fun u=>anisotropicMeasureTailPotential (anisotropicReplaceVariance D i u) μ q
      (anisotropicDisorderInjection n g+anisotropicFieldInjection n x))
      (anisotropicRestartVarianceResponse (anisotropicReplaceVariance D i b) μ g q x i) b := by
  apply hasDerivAt_of_all_moving_derivatives
    (fun j u=>anisotropicDyadicTailPotential (anisotropicReplaceVariance D i u) μ q j
      (anisotropicDisorderInjection n g+anisotropicFieldInjection n x))
    (fun j u=>anisotropicFiniteTailVarianceResponse (anisotropicReplaceVariance D i u)
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q
      (anisotropicDisorderInjection n g+anisotropicFieldInjection n x) i) _ b _ hb
  · intro j u hu
    exact hasDerivAt_anisotropicFiniteTailPotential_variance D
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q
      (anisotropicDisorderInjection n g+anisotropicFieldInjection n x) i u hu
  · intro u _
    exact tendsto_anisotropicDyadicTailPotential (anisotropicReplaceVariance D i u) μ q _
  · intro bj ht
    exact tendsto_anisotropicVarianceFiniteTailResponse D μ i hb ht g q x

end QuantitativeFollowup
