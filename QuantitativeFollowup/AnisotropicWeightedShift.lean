module
public import QuantitativeFollowup.AnisotropicShiftEnergy
public import QuantitativeFollowup.AnisotropicPosteriorMetric

@[expose] public section

/-! Actual signed Stieltjes score gradient and constructed posterior
inverse bound for every nonempty selected coordinate set. -/
noncomputable section
open Set QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1800000

def anisotropicPosteriorFeatureFinTime (i : anisotropicPosteriorFeatureIndex k) : Fin (k+3) :=
  ⟨anisotropicPosteriorFeatureTime i,by cases i <;> dsimp [anisotropicPosteriorFeatureTime] <;> omega⟩

def anisotropicPosteriorFeatureKernel (s : RSBScheme k) (kernel : ℝ→ℝ)
    (i : anisotropicPosteriorFeatureIndex k) : ℝ := kernel (s.q (anisotropicPosteriorFeatureTime i))

def anisotropicPosteriorSelfOverlapShift (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (J : Finset (Fin n)) (z : AnisotropicGaussianSpace n k) (i : anisotropicPosteriorFeatureIndex k) :
    AnisotropicGaussianSpace n k := anisotropicEuclideanSelfOverlapShift D s J (anisotropicPosteriorFeatureFinTime i) z

theorem anisotropicEuclideanWeightedSelfOverlapScore_eq_feature_sum (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (kernel : ℝ→ℝ) (J : Finset (Fin n)) :
    anisotropicEuclideanWeightedSelfOverlapScore D s a kernel J=fun z =>
      ∑i,anisotropicPosteriorFeatureWeight s a i*anisotropicPosteriorFeatureKernel s kernel i*
        anisotropicEuclideanSelfOverlapScore D s J (anisotropicPosteriorFeatureTime i) z := by
  classical
  funext z
  rw [Fintype.sum_option]
  simp only [anisotropicPosteriorFeatureWeight,anisotropicPosteriorFeatureKernel,anisotropicPosteriorFeatureTime,
    anisotropicEuclideanWeightedSelfOverlapScore]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (s.m (i+2)-s.m (i+1))*kernel (s.q (i+2))*
    anisotropicEuclideanSelfOverlapScore D s J (i+2) z)]

theorem anisotropicEuclideanWeightedSelfOverlapScore_gradient_shift (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (kernel : ℝ→ℝ) (J : Finset (Fin n)) (hJ : J.Nonempty)
    (z : AnisotropicGaussianSpace n k) :
    posteriorFeatureShift (anisotropicPosteriorFeatureHessian D s z)
      (anisotropicPosteriorFeatureWeight s a) (anisotropicPosteriorFeatureKernel s kernel)
      (anisotropicPosteriorSelfOverlapShift D s J z)=
      ((J.card : ℝ)/2) • gradient (anisotropicEuclideanWeightedSelfOverlapScore D s a kernel J) z := by
  classical
  rw [anisotropicEuclideanWeightedSelfOverlapScore_eq_feature_sum,gradient_finite_sum]
  · simp_rw [gradient_const_mul _
      ((boundedJets_anisotropicEuclideanSelfOverlapScore D s J _).1.differentiable (by simp))]
    unfold posteriorFeatureShift anisotropicPosteriorFeatureHessian anisotropicPosteriorSelfOverlapShift
    have ht' (i : anisotropicPosteriorFeatureIndex k) :
        hessianOperator (anisotropicEuclideanHistoryPotential D s (anisotropicPosteriorFeatureTime i)) z
          (anisotropicEuclideanSelfOverlapShift D s J (anisotropicPosteriorFeatureFinTime i) z)=
        ((J.card : ℝ)/2) • gradient (anisotropicEuclideanSelfOverlapScore D s J (anisotropicPosteriorFeatureTime i)) z :=
      anisotropicEuclideanSelfOverlapScore_hessian_shift_all D s J hJ (anisotropicPosteriorFeatureFinTime i) z
    simp_rw [ht',smul_comm _ ((J.card : ℝ)/2)]
    rw [Finset.smul_sum]
  · intro i _
    exact (contDiff_const.mul (boundedJets_anisotropicEuclideanSelfOverlapScore D s J _).1).differentiable (by simp)

theorem anisotropicEuclideanWeightedSelfOverlapScore_inverse_energy_le (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (ha : a ≤ s.m 1) (kernel : ℝ→ℝ)
    (J : Finset (Fin n)) (hJ : J.Nonempty) (σ : Configuration n) (z : AnisotropicGaussianSpace n k) :
    inner ℝ (gradient (anisotropicEuclideanWeightedSelfOverlapScore D s a kernel J) z)
      (Ring.inverse (hessianOperator (anisotropicPosteriorPotential D s a σ) z)
        (gradient (anisotropicEuclideanWeightedSelfOverlapScore D s a kernel J) z)) ≤
      (∑i,anisotropicPosteriorFeatureWeight s a i*(anisotropicPosteriorFeatureKernel s kernel i)^2*
        anisotropicSelfOverlapEnergy D s J (anisotropicPosteriorFeatureTime i) z)/((J.card : ℝ)/2)^2 := by
  classical
  have hcard : 0 < (J.card : ℝ) := by exact_mod_cast hJ.card_pos
  have hN : 0 < ((J.card : ℝ)/2)^2 := sq_pos_of_pos (by positivity)
  have hh := anisotropicPosteriorFeature_inverse_energy_le D s a ha σ z
    (anisotropicPosteriorFeatureKernel s kernel) (anisotropicPosteriorSelfOverlapShift D s J z)
  rw [anisotropicEuclideanWeightedSelfOverlapScore_gradient_shift D s a kernel J hJ z] at hh
  simp only [map_smul,real_inner_smul_left,real_inner_smul_right] at hh
  apply (le_div_iff₀ hN).mpr
  calc
    _ ≤ ∑i,anisotropicPosteriorFeatureWeight s a i*(anisotropicPosteriorFeatureKernel s kernel i)^2*
        inner ℝ (anisotropicPosteriorSelfOverlapShift D s J z i)
          (anisotropicPosteriorFeatureHessian D s z i (anisotropicPosteriorSelfOverlapShift D s J z i)) := by
      convert hh using 1 <;> ring
    _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
      (anisotropicEuclideanSelfOverlapShift_energy_le D s J (anisotropicPosteriorFeatureFinTime i) z)
      (mul_nonneg (anisotropicPosteriorFeatureWeight_nonneg s a ha i) (sq_nonneg _))

end QuantitativeFollowup
