module
public import QuantitativePaper.VectorFieldConditionalVariance

@[expose] public section

/-! Exact future-covariance decomposition of the actual finite Gaussian
recursion. Each future term is propagated by the genuine normalized kernel;
the positive CDF jumps, including the terminal jump, are retained. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128

def vectorFutureCovarianceCorrection {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b : Configuration n → ℝ) : ℕ → ℝ → Field n → ℝ
  | 0 => fun _ _ => 0
  | j+1 => fun y => vectorStepResponse ((1-t)*(β^2*(s.q (k+2-j)-s.q (k+1-j))))
      (s.m (k+1-j)) (vectorPerturbedRecursion s β t p b j y)
      (fun x => (observableDepthMass s j - observableDepthMass s (j+1)) *
        vectorObservableCovariance s β t p b j y x +
          vectorFutureCovarianceCorrection s β t p b j y x)

theorem vectorObservableSecondResponse_future_covariance {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n × ℝ) (b : Configuration n → ℝ)
    (R : ℝ≥0) (hb : ∀σ, |b σ| ≤ R) (j : ℕ) (y : ℝ) (x : Field n) :
    vectorObservableSecondResponse s β t p b j y x =
      observableDepthMass s j * vectorObservableCovariance s β t p b j y x +
        vectorFutureCovarianceCorrection s β t p b j y x := by
  induction j generalizing x with
  | zero =>
    simp only [vectorFutureCovarianceCorrection, observableDepthMass, ite_true,
      one_mul, add_zero, vectorObservableSecondResponse, vectorObservableCovariance,
      vectorConditionalMean, vectorObservableResponse, vectorTerminalObservable,
      terminalCovariance, pow_two]
  | succ j ih =>
    let f := vectorPerturbedRecursion s β t p b j y
    let v := vectorObservableResponse s β t p b j y
    let w := vectorConditionalMean s β t p b (fun σ => b σ^2) j y
    let H := vectorObservableSecondResponse s β t p b j y
    let C := vectorObservableCovariance s β t p b j y
    let c := (1-t)*(β^2*(s.q (k+2-j)-s.q (k+1-j)))
    let m := s.m (k+1-j)
    have hf := vectorPerturbedRecursion_lipschitz s β t p b j y
    have hv : Measurable v := (measurable_vectorObservableResponse s β t p b j).comp
      (measurable_const.prodMk measurable_id)
    have hw : Measurable w := (measurable_vectorConditionalMean s β t p b _ j).comp
      (measurable_const.prodMk measurable_id)
    have hH : Measurable H := (measurable_vectorObservableSecondResponse s β t p b j).comp
      (measurable_const.prodMk measurable_id)
    have hC : Measurable C := (measurable_vectorObservableCovariance s β t p b j).comp
      (measurable_const.prodMk measurable_id)
    have hbH (z) : |H z| ≤ observableSecondBound R j :=
      abs_vectorObservableSecondResponse_le s β t p b R hb j y z
    have hbC (z) : |C z| ≤ (R:ℝ)^2 := abs_vectorObservableCovariance_le s β t p b R hb j y z
    have hbmC (z) : |m*C z| ≤ |m| * (R:ℝ)^2 := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hbC z) (abs_nonneg m)
    have hbv2 (z) : |v z^2| ≤ (R:ℝ)^2 := by
      rw [abs_sq]
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (v z))
        (abs_vectorObservableResponse_le s β t p b R hb j y z) 2
    have hb2 (σ) : |b σ^2| ≤ (R:ℝ)^2 := by
      rw [abs_sq]
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (b σ)) (hb σ) 2
    have hbw (z) : |w z| ≤ (R:ℝ)^2 := abs_vectorConditionalMean_le s β t p b _ _ hb2 j y z
    have hmean : vectorStepResponse c m f C x =
        vectorStepResponse c m f w x - vectorStepResponse c m f (fun z => v z^2) x :=
      vectorStepResponse_sub f w (fun z => v z^2) _ hf hw (hv.pow_const 2)
        _ _ hbw hbv2 c m x
    have hin : (fun z => (observableDepthMass s j - observableDepthMass s (j+1))*C z +
        vectorFutureCovarianceCorrection s β t p b j y z) = fun z => H z - m*C z := by
      funext z
      have hi := ih z
      rw [observableDepthMass_succ]
      change (observableDepthMass s j - m)*C z + _ = H z - m*C z
      change H z = observableDepthMass s j*C z + _ at hi
      linarith
    have he : vectorFutureCovarianceCorrection s β t p b (j+1) y x =
        vectorStepResponse c m f H x - m*vectorStepResponse c m f C x := by
      change vectorStepResponse c m f
        (fun z => (observableDepthMass s j - observableDepthMass s (j+1))*C z +
          vectorFutureCovarianceCorrection s β t p b j y z) x = _
      rw [hin, vectorStepResponse_sub f H (fun z => m*C z) _ hf hH
        (hC.const_mul m) _ _ hbH hbmC c m x,
        vectorStepResponse_mul_const]
    rw [observableDepthMass_succ, he, hmean]
    change vectorStepSecondResponse c m f v H x =
      m*(vectorStepResponse c m f w x - (vectorStepResponse c m f v x)^2) +
        (vectorStepResponse c m f H x - m*(vectorStepResponse c m f w x -
          vectorStepResponse c m f (fun z => v z^2) x))
    unfold vectorStepSecondResponse
    ring

theorem vectorFieldHessian_future_covariance {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n × ℝ) (j : ℕ) (x w : Field n) :
    inner ℝ w (vectorFieldHessian s β t p j x w) =
      observableDepthMass s j *
        vectorObservableCovariance s β t p (fun σ => fieldDot w σ) j 0 x +
          vectorFutureCovarianceCorrection s β t p (fun σ => fieldDot w σ) j 0 x := by
  rw [vectorFieldHessian_quadratic_eq_secondResponse]
  exact vectorObservableSecondResponse_future_covariance s β t p _
    ⟨Real.sqrt (n:ℝ)*‖w‖, mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)⟩
    (abs_fieldDot w) j 0 x

end QuantitativePaper
