module
public import FourPapersCommon.VectorGaussianMoments

@[expose] public section

/-! The actual quadratic expectation identity in the finite-two-variable
multilinear representation used by `iteratedFDeriv`. -/
noncomputable section
open MeasureTheory ProbabilityTheory QuantitativePaper
open scoped BigOperators NNReal
namespace FourPapersCommon
set_option maxSynthPendingDepth 128
set_option maxHeartbeats 1000000

instance vectorTwoMeasurableSpace (n : ℕ) :
    MeasurableSpace (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Field n) ℝ) := borel _

instance vectorTwoBorelSpace (n : ℕ) :
    BorelSpace (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Field n) ℝ) := ⟨rfl⟩

def vectorBilinearOfTwoEquiv (n : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Field n) ℝ ≃ₗᵢ[ℝ]
      (Field n →L[ℝ] Field n →L[ℝ] ℝ) :=
  (continuousMultilinearCurryRightEquiv ℝ (fun _ : Fin 2 => Field n) ℝ).trans
    (continuousMultilinearCurryFin1 ℝ (Field n) (Field n →L[ℝ] ℝ))

def vectorBilinearOfTwoCLM (n : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Field n) ℝ →L[ℝ]
      (Field n →L[ℝ] Field n →L[ℝ] ℝ) :=
  (vectorBilinearOfTwoEquiv n).toContinuousLinearEquiv.toContinuousLinearMap

theorem vectorBilinearOfTwo_apply {n : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Field n) ℝ) (x y : Field n) :
    vectorBilinearOfTwoCLM n H x y = H ![x, y] := by
  change H (Fin.snoc (Fin.snoc 0 x) y) = H ![x, y]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem vectorBilinearOfTwo_diagonal {n : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Field n) ℝ) (x : Field n) :
    vectorBilinearOfTwoCLM n H x x = H (fun _ => x) := by
  rw [vectorBilinearOfTwo_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

def vectorTwoTrace {n : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Field n) ℝ) : ℝ :=
  ∑ i : Fin n, H (fun _ => EuclideanSpace.single i 1)

theorem vectorBilinearTrace_of_two {n : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Field n) ℝ) :
    vectorBilinearTrace (vectorBilinearOfTwoCLM n H) = vectorTwoTrace H := by
  simp only [vectorBilinearTrace, vectorTwoTrace, vectorBilinearOfTwo_diagonal]

theorem integral_increment_two {n : ℕ} (r t : ℝ≥0) (hrt : r ≤ t)
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Field n) ℝ) :
    (∫ ω, H (fun _ => disorderVectorBrownianIncrement r t ω)
      ∂vectorDisorderBrownianMeasure n) = ((t : ℝ) - r) * vectorTwoTrace H := by
  simpa only [vectorBilinearOfTwo_diagonal, vectorBilinearTrace_of_two] using
    integral_increment_bilinear r t hrt (vectorBilinearOfTwoCLM n H)

theorem integrable_known_two_increment {n : ℕ} (r t : ℝ≥0) (hrt : r ≤ t)
    (H : VectorDisorderBrownianSample n →
      ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Field n) ℝ)
    (hH : Measurable[vectorBrownianFiltration n r] H)
    (hiH : Integrable H (vectorDisorderBrownianMeasure n)) :
    Integrable (fun ω => H ω (fun _ => disorderVectorBrownianIncrement r t ω))
      (vectorDisorderBrownianMeasure n) := by
  simpa only [vectorBilinearOfTwo_diagonal] using integrable_known_bilinear_increment r t hrt
    (fun ω => vectorBilinearOfTwoCLM n (H ω))
    ((vectorBilinearOfTwoCLM n).continuous.measurable.comp hH)
    ((vectorBilinearOfTwoCLM n).integrable_comp hiH)

theorem integral_known_two_increment {n : ℕ} (r t : ℝ≥0) (hrt : r ≤ t)
    (H : VectorDisorderBrownianSample n →
      ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Field n) ℝ)
    (hH : Measurable[vectorBrownianFiltration n r] H)
    (hiH : Integrable H (vectorDisorderBrownianMeasure n)) :
    (∫ ω, H ω (fun _ => disorderVectorBrownianIncrement r t ω)
      ∂vectorDisorderBrownianMeasure n) =
      ((t : ℝ) - r) * ∫ ω, vectorTwoTrace (H ω) ∂vectorDisorderBrownianMeasure n := by
  simpa only [vectorBilinearOfTwo_diagonal, vectorBilinearTrace_of_two] using
    integral_known_bilinear_increment r t hrt (fun ω => vectorBilinearOfTwoCLM n (H ω))
      ((vectorBilinearOfTwoCLM n).continuous.measurable.comp hH)
      ((vectorBilinearOfTwoCLM n).integrable_comp hiH)

theorem integrable_vectorTwoTrace {n : ℕ}
    (H : VectorDisorderBrownianSample n →
      ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Field n) ℝ)
    (hiH : Integrable H (vectorDisorderBrownianMeasure n)) :
    Integrable (fun ω => vectorTwoTrace (H ω)) (vectorDisorderBrownianMeasure n) := by
  have hiB := (vectorBilinearOfTwoCLM n).integrable_comp hiH
  have hiS := integrable_finsetSum Finset.univ (fun (i : Fin n) _ =>
    (hiB.apply_continuousLinearMap (EuclideanSpace.single i 1)).apply_continuousLinearMap
      (EuclideanSpace.single i 1))
  simpa only [vectorBilinearOfTwo_diagonal, vectorTwoTrace] using hiS

theorem integral_known_two_increment_centered {n : ℕ} (r t : ℝ≥0) (hrt : r ≤ t)
    (H : VectorDisorderBrownianSample n →
      ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Field n) ℝ)
    (hH : Measurable[vectorBrownianFiltration n r] H)
    (hiH : Integrable H (vectorDisorderBrownianMeasure n)) :
    (∫ ω, H ω (fun _ => disorderVectorBrownianIncrement r t ω) -
      ((t : ℝ) - r) * vectorTwoTrace (H ω) ∂vectorDisorderBrownianMeasure n) = 0 := by
  rw [integral_sub (integrable_known_two_increment r t hrt H hH hiH)
    ((integrable_vectorTwoTrace H hiH).const_mul _), integral_const_mul,
    integral_known_two_increment r t hrt H hH hiH, sub_self]

end FourPapersCommon
