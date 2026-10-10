module
public import QuantitativeFollowup.AnisotropicMagnetization
public import QuantitativeFollowup.AnisotropicPosteriorBL
public import QuantitativeFollowup.AnisotropicPosteriorMetric

@[expose] public section

/-! The literal selected-coordinate self-overlap and signed finite
Stieltjes score of the actual anisotropic model. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1600000

def anisotropicEuclideanSelfOverlapScore (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (J : Finset (Fin n)) (i : ℕ) (z : AnisotropicGaussianSpace n k) : ℝ :=
  (∑l ∈ J,(anisotropicEuclideanMagnetization D s i z l)^2)/(J.card : ℝ)

def anisotropicEuclideanWeightedSelfOverlapScore (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (kernel : ℝ→ℝ) (J : Finset (Fin n)) (z : AnisotropicGaussianSpace n k) : ℝ :=
  (s.m 1-a)*kernel (s.q 1)*anisotropicEuclideanSelfOverlapScore D s J 1 z+
    ∑i ∈ Finset.range k,(s.m (i+2)-s.m (i+1))*kernel (s.q (i+2))*
      anisotropicEuclideanSelfOverlapScore D s J (i+2) z

theorem boundedJets_anisotropicEuclideanSelfOverlapScore (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : Finset (Fin n)) (i : ℕ) :
    BoundedJets (anisotropicEuclideanSelfOverlapScore D s J i) := by
  have hs := boundedJets_finite_sum J
    (fun l z => anisotropicEuclideanMagnetization D s i z l*anisotropicEuclideanMagnetization D s i z l)
    (fun l _ => (boundedJets_anisotropicEuclideanMagnetization_component D s i l).mul
      (boundedJets_anisotropicEuclideanMagnetization_component D s i l))
  have he : anisotropicEuclideanSelfOverlapScore D s J i=fun z =>
      (J.card : ℝ)⁻¹*(∑l ∈ J,anisotropicEuclideanMagnetization D s i z l*
        anisotropicEuclideanMagnetization D s i z l) := by
    funext z
    simp only [anisotropicEuclideanSelfOverlapScore,pow_two,div_eq_mul_inv,mul_comm]
  rw [he]
  exact hs.const_mul _

theorem boundedJets_anisotropicEuclideanWeightedSelfOverlapScore (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (kernel : ℝ→ℝ) (J : Finset (Fin n)) :
    BoundedJets (anisotropicEuclideanWeightedSelfOverlapScore D s a kernel J) :=
  ((boundedJets_anisotropicEuclideanSelfOverlapScore D s J 1).const_mul _).add
    (boundedJets_finite_sum (Finset.range k)
      (fun i z => (s.m (i+2)-s.m (i+1))*kernel (s.q (i+2))*
        anisotropicEuclideanSelfOverlapScore D s J (i+2) z)
      (fun i _ => (boundedJets_anisotropicEuclideanSelfOverlapScore D s J (i+2)).const_mul _))

theorem anisotropicEuclideanSelfOverlapScore_gauge (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (J : Finset (Fin n)) (η : Configuration n) (i : ℕ)
    (z : AnisotropicGaussianSpace n k) :
    anisotropicEuclideanSelfOverlapScore D s J i (anisotropicGaussianGauge η z)=
      anisotropicEuclideanSelfOverlapScore D s J i z := by
  unfold anisotropicEuclideanSelfOverlapScore
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [anisotropicEuclideanMagnetization_component_gauge]
  cases hη : η l <;> simp [Paper.spinSign,hη]

theorem anisotropicEuclideanWeightedSelfOverlapScore_gauge (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (kernel : ℝ→ℝ) (J : Finset (Fin n))
    (η : Configuration n) (z : AnisotropicGaussianSpace n k) :
    anisotropicEuclideanWeightedSelfOverlapScore D s a kernel J (anisotropicGaussianGauge η z)=
      anisotropicEuclideanWeightedSelfOverlapScore D s a kernel J z := by
  simp only [anisotropicEuclideanWeightedSelfOverlapScore,anisotropicEuclideanSelfOverlapScore_gauge]

theorem anisotropicWeightedSelfOverlapScore_posterior_means (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (kernel : ℝ→ℝ) (J : Finset (Fin n)) (σ τ : Configuration n) :
    (∫z,anisotropicEuclideanWeightedSelfOverlapScore D s a kernel J z ∂anisotropicSpinPosteriorLaw D s a σ)=
      ∫z,anisotropicEuclideanWeightedSelfOverlapScore D s a kernel J z ∂anisotropicSpinPosteriorLaw D s a τ :=
  anisotropicSpinPosterior_invariant_means D s a
    (fun _ => anisotropicEuclideanWeightedSelfOverlapScore D s a kernel J)
    (fun η _ z => anisotropicEuclideanWeightedSelfOverlapScore_gauge D s a kernel J η z) σ τ

theorem anisotropicSpinPosterior_weightedSelfOverlap_brascamp_lieb [Nonempty (Fin n)]
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0)
    (ha : a ≤ s.m 1) (kernel : ℝ→ℝ) (J : Finset (Fin n)) (σ : Configuration n) :
    variance (anisotropicEuclideanWeightedSelfOverlapScore D s a kernel J)
      (anisotropicSpinPosteriorLaw D s a σ) ≤
      ∫z,inner ℝ (gradient (anisotropicEuclideanWeightedSelfOverlapScore D s a kernel J) z)
        (Ring.inverse (hessianOperator (anisotropicPosteriorPotential D s a σ) z)
          (gradient (anisotropicEuclideanWeightedSelfOverlapScore D s a kernel J) z))
        ∂anisotropicSpinPosteriorLaw D s a σ :=
  anisotropicSpinPosterior_brascamp_lieb s D a hq ha σ _
    (boundedJets_anisotropicEuclideanWeightedSelfOverlapScore D s a kernel J)

end QuantitativeFollowup
