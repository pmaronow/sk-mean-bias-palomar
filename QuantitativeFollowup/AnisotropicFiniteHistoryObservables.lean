module
public import QuantitativeFollowup.AnisotropicCovarianceIntegration
public import QuantitativeFollowup.AnisotropicFiniteNodeResponse

@[expose] public section

/-! Literal selected-coordinate spin means, Hessian energies and covariance
 energies as functions of the complete finite anisotropic history. Their
 coordinate-chart pullbacks are exactly the already proved posterior tests. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1000000

def anisotropicHistoryMagnetization (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : ℕ) (h : FiniteHistory (AnisotropicParameter n) (k+2)) : Field n :=
  anisotropicMagnetization D s (k+2-i) (historyExtended h i)

theorem continuous_anisotropicHistoryMagnetization (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : ℕ) : Continuous (anisotropicHistoryMagnetization D s i) := by
  change Continuous (fun h : FiniteHistory (AnisotropicParameter n) (k+2)=>anisotropicResponseMap n
    (fderiv ℝ (anisotropicFinitePotential D s (k+2-i)) (h (Fin.ofNat (k+3) i))))
  have hd : ContDiff ℝ ∞ (fderiv ℝ (anisotropicFinitePotential D s (k+2-i))) :=
    (contDiff_anisotropicFinitePotential D s _).fderiv_right (by simp)
  have hp : Continuous (fun h : FiniteHistory (AnisotropicParameter n) (k+2) =>
      h (Fin.ofNat (k+3) i)) := continuous_apply _
  exact (anisotropicResponseMap n).continuous.comp (hd.continuous.comp hp)

def anisotropicHistorySelectedMean (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (J : Finset (Fin n)) (i : ℕ) (h : FiniteHistory (AnisotropicParameter n) (k+2)) : Field n :=
  anisotropicSelectedInsertion J (anisotropicSelectedProjection J (anisotropicHistoryMagnetization D s i h))

theorem continuous_anisotropicHistorySelectedMean (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : Finset (Fin n)) (i : ℕ) :
    Continuous (anisotropicHistorySelectedMean D s J i) :=
  (anisotropicSelectedInsertion J).continuous.comp
    ((anisotropicSelectedProjection J).continuous.comp (continuous_anisotropicHistoryMagnetization D s i))

def anisotropicHistorySelfOverlap (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (J : Finset (Fin n)) (i : ℕ) (h : FiniteHistory (AnisotropicParameter n) (k+2)) : ℝ :=
  (∑l∈J,(anisotropicHistoryMagnetization D s i h l)^2)/(J.card : ℝ)

def anisotropicHistoryWeightedSelfOverlap (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (kernel : ℝ→ℝ) (J : Finset (Fin n)) (h : FiniteHistory (AnisotropicParameter n) (k+2)) : ℝ :=
  ∑i,anisotropicPosteriorFeatureWeight s a i*anisotropicPosteriorFeatureKernel s kernel i*
    anisotropicHistorySelfOverlap D s J (anisotropicPosteriorFeatureTime i) h

theorem continuous_anisotropicHistoryWeightedSelfOverlap (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (kernel : ℝ→ℝ) (J : Finset (Fin n)) :
    Continuous (anisotropicHistoryWeightedSelfOverlap D s a kernel J) := by
  unfold anisotropicHistoryWeightedSelfOverlap
  apply continuous_finset_sum
  intro i _
  apply continuous_const.mul
  unfold anisotropicHistorySelfOverlap
  apply Continuous.div_const
  apply continuous_finset_sum
  intro l _
  exact ((EuclideanSpace.proj l).continuous.comp
    (continuous_anisotropicHistoryMagnetization D s _)).pow 2

def anisotropicHistoryHessianEnergy (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (J : Finset (Fin n)) (i : ℕ) (h : FiniteHistory (AnisotropicParameter n) (k+2)) : ℝ :=
  inner ℝ (anisotropicHistorySelectedMean D s J i h)
    (anisotropicFieldHessian D s (k+2-i) (historyExtended h i)
      (anisotropicHistorySelectedMean D s J i h))

theorem continuous_anisotropicHistoryHessianEnergy (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : Finset (Fin n)) (i : ℕ) :
    Continuous (anisotropicHistoryHessianEnergy D s J i) := by
  let U:=anisotropicFinitePotential D s (k+2-i)
  let v:=fun h : FiniteHistory (AnisotropicParameter n) (k+2)=>
    anisotropicFieldInjection n (anisotropicHistorySelectedMean D s J i h)
  have hv : Continuous v:=(anisotropicFieldInjection n).continuous.comp
    (continuous_anisotropicHistorySelectedMean D s J i)
  have hd1 : ContDiff ℝ ∞ (fderiv ℝ U):=
    (contDiff_anisotropicFinitePotential D s (k+2-i)).fderiv_right (by simp)
  have hd : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ U)):=hd1.fderiv_right (by simp)
  have he : anisotropicHistoryHessianEnergy D s J i=fun h=>
    fderiv ℝ (fderiv ℝ U) (h (Fin.ofNat (k+3) i)) (v h) (v h) := by
    funext h
    exact anisotropicFieldHessian_quadratic_eq_parameter D s _ _ _
  rw [he]
  have hp : Continuous (fun h : FiniteHistory (AnisotropicParameter n) (k+2) =>
      h (Fin.ofNat (k+3) i)) := continuous_apply _
  have hh := (hd.continuous.comp hp).clm_apply hv
  have hh2 := hh.clm_apply hv
  simpa only [Function.comp_def] using hh2

def anisotropicHistoryWeightedHessianEnergy (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (kernel : ℝ→ℝ) (J : Finset (Fin n)) (h : FiniteHistory (AnisotropicParameter n) (k+2)) : ℝ :=
  (∑i,anisotropicPosteriorFeatureWeight s a i*(anisotropicPosteriorFeatureKernel s kernel i)^2*
    anisotropicHistoryHessianEnergy D s J (anisotropicPosteriorFeatureTime i) h)/((J.card : ℝ)/2)^2

theorem continuous_anisotropicHistoryWeightedHessianEnergy (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (kernel : ℝ→ℝ) (J : Finset (Fin n)) :
    Continuous (anisotropicHistoryWeightedHessianEnergy D s a kernel J) := by
  unfold anisotropicHistoryWeightedHessianEnergy
  exact (continuous_finset_sum _ (fun i _=>continuous_const.mul
    (continuous_anisotropicHistoryHessianEnergy D s J _))).div_const _

def anisotropicHistoryCovarianceEnergy (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (J : Finset (Fin n)) (i : ℕ) (h : FiniteHistory (AnisotropicParameter n) (k+2)) : ℝ :=
  anisotropicSpinCovarianceEnergy D s (k+2-i) (historyExtended h i)
    (anisotropicHistorySelectedMean D s J i h)

theorem continuous_anisotropicHistoryCovarianceEnergy (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : Finset (Fin n)) (i : ℕ) :
    Continuous (anisotropicHistoryCovarianceEnergy D s J i) := by
  have hp : Continuous (fun h : FiniteHistory (AnisotropicParameter n) (k+2)=>historyExtended h i):=
    continuous_apply _
  unfold anisotropicHistoryCovarianceEnergy
  simpa only [Function.comp_def] using
    (continuous_anisotropicSpinCovarianceEnergy D s (k+2-i)).comp
      (hp.prodMk (continuous_anisotropicHistorySelectedMean D s J i))

def anisotropicHistoryWeightedCovarianceEnergy (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (kernel : ℝ→ℝ) (J : Finset (Fin n)) (h : FiniteHistory (AnisotropicParameter n) (k+2)) : ℝ :=
  (∑i,anisotropicPosteriorFeatureWeight s a i*(anisotropicPosteriorFeatureKernel s kernel i)^2*
    anisotropicHistoryCovarianceEnergy D s J (anisotropicPosteriorFeatureTime i) h)/((J.card : ℝ)/2)^2

theorem continuous_anisotropicHistoryWeightedCovarianceEnergy (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (kernel : ℝ→ℝ) (J : Finset (Fin n)) :
    Continuous (anisotropicHistoryWeightedCovarianceEnergy D s a kernel J) := by
  unfold anisotropicHistoryWeightedCovarianceEnergy
  exact (continuous_finset_sum _ (fun i _=>continuous_const.mul
    (continuous_anisotropicHistoryCovarianceEnergy D s J _))).div_const _

theorem anisotropicHistoryMagnetization_chart (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : ℕ) (p : AnisotropicGaussianSpace n k×Configuration n) :
    anisotropicHistoryMagnetization D s i (anisotropicEuclideanJointMap D s p).1=
      anisotropicEuclideanMagnetization D s i p.1 := by
  rw [anisotropicEuclideanMagnetization,anisotropicEuclideanStateLinear_apply]
  rfl

theorem anisotropicHistoryWeightedSelfOverlap_chart (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (kernel : ℝ→ℝ) (J : Finset (Fin n))
    (p : AnisotropicGaussianSpace n k×Configuration n) :
    anisotropicHistoryWeightedSelfOverlap D s a kernel J (anisotropicEuclideanJointMap D s p).1=
      anisotropicEuclideanWeightedSelfOverlapScore D s a kernel J p.1 := by
  rw [anisotropicEuclideanWeightedSelfOverlapScore_eq_feature_sum]
  simp only [anisotropicHistoryWeightedSelfOverlap,anisotropicHistorySelfOverlap,
    anisotropicHistoryMagnetization_chart,anisotropicEuclideanSelfOverlapScore]

theorem anisotropicHistoryWeightedHessianEnergy_chart (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (kernel : ℝ→ℝ) (J : Finset (Fin n))
    (p : AnisotropicGaussianSpace n k×Configuration n) :
    anisotropicHistoryWeightedHessianEnergy D s a kernel J (anisotropicEuclideanJointMap D s p).1=
      anisotropicWeightedHessianEnergy D s a kernel J p.1 := by
  unfold anisotropicHistoryWeightedHessianEnergy anisotropicWeightedHessianEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  unfold anisotropicHistoryHessianEnergy anisotropicSelfOverlapEnergy anisotropicHistorySelectedMean
    anisotropicSelectedMean anisotropicSelectedMagnetization
  rw [anisotropicHistoryMagnetization_chart,anisotropicEuclideanStateLinear_apply]
  rfl

theorem anisotropicHistoryWeightedCovarianceEnergy_chart (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (kernel : ℝ→ℝ) (J : Finset (Fin n))
    (p : AnisotropicGaussianSpace n k×Configuration n) :
    anisotropicHistoryWeightedCovarianceEnergy D s a kernel J (anisotropicEuclideanJointMap D s p).1=
      anisotropicWeightedCovarianceEnergy D s a kernel J p.1 := by
  unfold anisotropicHistoryWeightedCovarianceEnergy anisotropicWeightedCovarianceEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  unfold anisotropicHistoryCovarianceEnergy anisotropicSelfOverlapCovarianceEnergy anisotropicHistorySelectedMean
    anisotropicSelectedMean anisotropicSelectedMagnetization
  rw [anisotropicHistoryMagnetization_chart,anisotropicEuclideanStateLinear_apply]
  rfl

end QuantitativeFollowup
