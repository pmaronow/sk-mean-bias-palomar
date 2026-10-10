module
public import QuantitativePaper.VectorBrownianMoments
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry

@[expose] public section

/-! Actual vector Brownian linear and quadratic moments.  Random
coefficients are known in the enlarged natural past, which already includes
the independent initial disorder.  No independence or cancellation law is
assumed for the actual increment. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set QuantitativePaper
open scoped BigOperators NNReal ENNReal
namespace FourPapersCommon
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

def vectorBilinearTrace {n : ℕ} (H : Field n →L[ℝ] Field n →L[ℝ] ℝ) : ℝ :=
  ∑ i : Fin n, H (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)

theorem vector_linear_apply_eq_sum {n : ℕ} (L : Field n →L[ℝ] ℝ) (x : Field n) :
    L x = ∑ i : Fin n, L (EuclideanSpace.single i 1) * x i := by
  have hx : x = ∑ i : Fin n, x i • EuclideanSpace.single i 1 := by
    ext i
    simp [Pi.single_apply]
  conv_lhs => rw [hx]
  simp only [map_sum, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem vector_bilinear_apply_eq_sum {n : ℕ}
    (H : Field n →L[ℝ] Field n →L[ℝ] ℝ) (x y : Field n) :
    H x y = ∑ i : Fin n, ∑ j : Fin n,
      H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) * (x i * y j) := by
  have hx : x = ∑ i : Fin n, x i • EuclideanSpace.single i 1 := by
    ext i
    simp [Pi.single_apply]
  conv_lhs => rw [hx]
  simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [vector_linear_apply_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem integrable_increment {n : ℕ} (r t : ℝ≥0) (hrt : r ≤ t) :
    Integrable (disorderVectorBrownianIncrement (n := n) r t)
      (vectorDisorderBrownianMeasure n) := by
  apply (integrable_norm_iff
    (measurable_disorderVectorBrownianIncrement r t).aestronglyMeasurable).mp
  simpa only [pow_one] using integrable_disorderVectorBrownianIncrement_norm_pow r t hrt 1

theorem integral_increment {n : ℕ} (r t : ℝ≥0) (hrt : r ≤ t) :
    (∫ ω, disorderVectorBrownianIncrement (n := n) r t ω
      ∂vectorDisorderBrownianMeasure n) = 0 := by
  ext i
  have H := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).integral_comp_comm (integrable_increment r t hrt)
  change (∫ ω, disorderVectorBrownianIncrement r t ω i ∂vectorDisorderBrownianMeasure n) =
    (∫ ω, disorderVectorBrownianIncrement r t ω ∂vectorDisorderBrownianMeasure n) i at H
  rw [integral_disorderVectorBrownianIncrement_coordinate r t hrt i] at H
  simpa only [PiLp.proj_apply, PiLp.zero_apply] using H.symm

theorem integral_increment_CLM {n : ℕ} (r t : ℝ≥0) (hrt : r ≤ t)
    (L : Field n →L[ℝ] ℝ) :
    (∫ ω, L (disorderVectorBrownianIncrement r t ω)
      ∂vectorDisorderBrownianMeasure n) = 0 := by
  rw [L.integral_comp_comm (integrable_increment r t hrt), integral_increment r t hrt]
  exact map_zero L

theorem integrable_increment_coordinates_mul {n : ℕ} (r t : ℝ≥0) (hrt : r ≤ t)
    (i j : Fin n) :
    Integrable (fun ω => disorderVectorBrownianIncrement r t ω i *
      disorderVectorBrownianIncrement r t ω j) (vectorDisorderBrownianMeasure n) := by
  have hi := (show Measurable (fun z : Field n => z i) from by fun_prop).comp
    (measurable_disorderVectorBrownianIncrement r t)
  have hj := (show Measurable (fun z : Field n => z j) from by fun_prop).comp
    (measurable_disorderVectorBrownianIncrement r t)
  apply (integrable_disorderVectorBrownianIncrement_norm_pow r t hrt 2).mono'
    (hi.mul hj).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  change ‖disorderVectorBrownianIncrement r t ω i * disorderVectorBrownianIncrement r t ω j‖ ≤ _
  rw [norm_mul]
  calc
    _ ≤ ‖disorderVectorBrownianIncrement r t ω‖ * ‖disorderVectorBrownianIncrement r t ω‖ :=
      mul_le_mul (PiLp.norm_apply_le _ _) (PiLp.norm_apply_le _ _) (norm_nonneg _) (norm_nonneg _)
    _ = _ := (pow_two _).symm

theorem integral_increment_norm_sq {n : ℕ} (r t : ℝ≥0) (hrt : r ≤ t) :
    (∫ ω, ‖disorderVectorBrownianIncrement (n := n) r t ω‖ ^ 2
      ∂vectorDisorderBrownianMeasure n) = (n : ℝ) * ((t : ℝ) - r) := by
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum Finset.univ (fun i _ => by
    simpa only [pow_two] using integrable_increment_coordinates_mul r t hrt i i)]
  simp only [integral_square_disorderVectorBrownianIncrement_coordinate r t hrt,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem integral_increment_bilinear {n : ℕ} (r t : ℝ≥0) (hrt : r ≤ t)
    (H : Field n →L[ℝ] Field n →L[ℝ] ℝ) :
    (∫ ω, H (disorderVectorBrownianIncrement r t ω) (disorderVectorBrownianIncrement r t ω)
      ∂vectorDisorderBrownianMeasure n) = ((t : ℝ) - r) * vectorBilinearTrace H := by
  have he : (fun ω => H (disorderVectorBrownianIncrement r t ω)
      (disorderVectorBrownianIncrement r t ω)) =
      (fun ω => ∑ i : Fin n, ∑ j : Fin n,
        H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) *
          (disorderVectorBrownianIncrement r t ω i * disorderVectorBrownianIncrement r t ω j)) :=
    funext fun ω => vector_bilinear_apply_eq_sum H _ _
  rw [he]
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ =>
    (integrable_increment_coordinates_mul r t hrt i j).const_mul _))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ =>
    (integrable_increment_coordinates_mul r t hrt _ j).const_mul _), integral_const_mul,
    integral_cross_disorderVectorBrownianIncrement_coordinates r t hrt]
  simp [vectorBilinearTrace, Finset.mul_sum, mul_comm]

theorem integrable_known_mul_increment_coordinate {n : ℕ}
    (r t : ℝ≥0) (hrt : r ≤ t) (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltration n r] Z)
    (hiZ : Integrable Z (vectorDisorderBrownianMeasure n)) (i : Fin n) :
    Integrable (fun ω => Z ω * disorderVectorBrownianIncrement r t ω i)
      (vectorDisorderBrownianMeasure n) := by
  have hI : IndepFun Z (fun ω => disorderVectorBrownianIncrement r t ω i)
      (vectorDisorderBrownianMeasure n) := by
    simpa only [Function.comp_def, id_eq] using
      (indep_disorderVectorBrownianIncrement_known r t hrt Z hZ).symm.comp
        measurable_id (show Measurable (fun z : Field n => z i) from by fun_prop)
  exact hI.integrable_mul hiZ ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).integrable_comp
    (integrable_increment r t hrt))

theorem integral_known_mul_increment_coordinate {n : ℕ}
    (r t : ℝ≥0) (hrt : r ≤ t) (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltration n r] Z)
    (hiZ : Integrable Z (vectorDisorderBrownianMeasure n)) (i : Fin n) :
    (∫ ω, Z ω * disorderVectorBrownianIncrement r t ω i
      ∂vectorDisorderBrownianMeasure n) = 0 := by
  have hI : IndepFun Z (fun ω => disorderVectorBrownianIncrement r t ω i)
      (vectorDisorderBrownianMeasure n) := by
    simpa only [Function.comp_def, id_eq] using
      (indep_disorderVectorBrownianIncrement_known r t hrt Z hZ).symm.comp
        measurable_id (show Measurable (fun z : Field n => z i) from by fun_prop)
  have hi := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).integrable_comp
    (integrable_increment r t hrt)
  rw [hI.integral_fun_mul_eq_mul_integral hiZ.aestronglyMeasurable hi.aestronglyMeasurable,
    integral_disorderVectorBrownianIncrement_coordinate r t hrt i, mul_zero]

theorem integrable_known_mul_increment_coordinates {n : ℕ}
    (r t : ℝ≥0) (hrt : r ≤ t) (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltration n r] Z)
    (hiZ : Integrable Z (vectorDisorderBrownianMeasure n)) (i j : Fin n) :
    Integrable (fun ω => Z ω * (disorderVectorBrownianIncrement r t ω i *
      disorderVectorBrownianIncrement r t ω j)) (vectorDisorderBrownianMeasure n) := by
  have hI : IndepFun Z (fun ω => disorderVectorBrownianIncrement r t ω i *
      disorderVectorBrownianIncrement r t ω j) (vectorDisorderBrownianMeasure n) := by
    simpa only [Function.comp_def, id_eq] using
      (indep_disorderVectorBrownianIncrement_known r t hrt Z hZ).symm.comp
        measurable_id (show Measurable (fun z : Field n => z i * z j) from by fun_prop)
  exact hI.integrable_mul hiZ (integrable_increment_coordinates_mul r t hrt i j)

theorem integral_known_mul_increment_coordinates {n : ℕ}
    (r t : ℝ≥0) (hrt : r ≤ t) (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltration n r] Z)
    (hiZ : Integrable Z (vectorDisorderBrownianMeasure n)) (i j : Fin n) :
    (∫ ω, Z ω * (disorderVectorBrownianIncrement r t ω i *
      disorderVectorBrownianIncrement r t ω j) ∂vectorDisorderBrownianMeasure n) =
      (∫ ω, Z ω ∂vectorDisorderBrownianMeasure n) * (if i = j then (t : ℝ) - r else 0) := by
  have hI : IndepFun Z (fun ω => disorderVectorBrownianIncrement r t ω i *
      disorderVectorBrownianIncrement r t ω j) (vectorDisorderBrownianMeasure n) := by
    simpa only [Function.comp_def, id_eq] using
      (indep_disorderVectorBrownianIncrement_known r t hrt Z hZ).symm.comp
        measurable_id (show Measurable (fun z : Field n => z i * z j) from by fun_prop)
  rw [hI.integral_fun_mul_eq_mul_integral hiZ.aestronglyMeasurable
    (integrable_increment_coordinates_mul r t hrt i j).aestronglyMeasurable,
    integral_cross_disorderVectorBrownianIncrement_coordinates r t hrt i j]

theorem integrable_known_CLM_increment {n : ℕ} (r t : ℝ≥0) (hrt : r ≤ t)
    (L : VectorDisorderBrownianSample n → (Field n →L[ℝ] ℝ))
    (hL : Measurable[vectorBrownianFiltration n r] L)
    (hiL : Integrable L (vectorDisorderBrownianMeasure n)) :
    Integrable (fun ω => L ω (disorderVectorBrownianIncrement r t ω))
      (vectorDisorderBrownianMeasure n) := by
  exact (indep_disorderVectorBrownianIncrement_known r t hrt L hL).symm.integrable_bilin
    hiL (integrable_increment r t hrt) (ContinuousLinearMap.apply ℝ ℝ).flip

theorem integral_known_CLM_increment {n : ℕ} (r t : ℝ≥0) (hrt : r ≤ t)
    (L : VectorDisorderBrownianSample n → (Field n →L[ℝ] ℝ))
    (hL : Measurable[vectorBrownianFiltration n r] L)
    (hiL : Integrable L (vectorDisorderBrownianMeasure n)) :
    (∫ ω, L ω (disorderVectorBrownianIncrement r t ω)
      ∂vectorDisorderBrownianMeasure n) = 0 := by
  have H := (indep_disorderVectorBrownianIncrement_known r t hrt L hL).symm.integral_bilin
    hiL (integrable_increment r t hrt) (ContinuousLinearMap.apply ℝ ℝ).flip
  simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.apply_apply,
    integral_increment r t hrt, map_zero] using H

theorem integrable_known_bilinear_increment {n : ℕ} (r t : ℝ≥0) (hrt : r ≤ t)
    (H : VectorDisorderBrownianSample n → (Field n →L[ℝ] Field n →L[ℝ] ℝ))
    (hH : Measurable[vectorBrownianFiltration n r] H)
    (hiH : Integrable H (vectorDisorderBrownianMeasure n)) :
    Integrable (fun ω => H ω (disorderVectorBrownianIncrement r t ω)
      (disorderVectorBrownianIncrement r t ω)) (vectorDisorderBrownianMeasure n) := by
  have he : (fun ω => H ω (disorderVectorBrownianIncrement r t ω)
      (disorderVectorBrownianIncrement r t ω)) =
      (fun ω => ∑ i : Fin n, ∑ j : Fin n,
        H ω (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) *
          (disorderVectorBrownianIncrement r t ω i * disorderVectorBrownianIncrement r t ω j)) :=
    funext fun ω => vector_bilinear_apply_eq_sum (H ω) _ _
  rw [he]
  apply integrable_finsetSum Finset.univ
  intro i _
  apply integrable_finsetSum Finset.univ
  intro j _
  exact integrable_known_mul_increment_coordinates r t hrt _
    ((show Measurable (fun A : Field n →L[ℝ] Field n →L[ℝ] ℝ =>
      A (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) from by fun_prop).comp hH)
    ((hiH.apply_continuousLinearMap _).apply_continuousLinearMap _) i j

theorem integral_known_bilinear_increment {n : ℕ} (r t : ℝ≥0) (hrt : r ≤ t)
    (H : VectorDisorderBrownianSample n → (Field n →L[ℝ] Field n →L[ℝ] ℝ))
    (hH : Measurable[vectorBrownianFiltration n r] H)
    (hiH : Integrable H (vectorDisorderBrownianMeasure n)) :
    (∫ ω, H ω (disorderVectorBrownianIncrement r t ω)
      (disorderVectorBrownianIncrement r t ω) ∂vectorDisorderBrownianMeasure n) =
        ((t : ℝ) - r) * ∫ ω, vectorBilinearTrace (H ω) ∂vectorDisorderBrownianMeasure n := by
  have hc (i j : Fin n) : Measurable[vectorBrownianFiltration n r]
      (fun ω => H ω (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) :=
    (show Measurable (fun A : Field n →L[ℝ] Field n →L[ℝ] ℝ =>
      A (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) from by fun_prop).comp hH
  have hic (i j : Fin n) : Integrable
      (fun ω => H ω (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
      (vectorDisorderBrownianMeasure n) :=
    (hiH.apply_continuousLinearMap _).apply_continuousLinearMap _
  have hip (i j : Fin n) := integrable_known_mul_increment_coordinates r t hrt _ (hc i j) (hic i j) i j
  have he : (fun ω => H ω (disorderVectorBrownianIncrement r t ω)
      (disorderVectorBrownianIncrement r t ω)) =
      (fun ω => ∑ i : Fin n, ∑ j : Fin n,
        H ω (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) *
          (disorderVectorBrownianIncrement r t ω i * disorderVectorBrownianIncrement r t ω j)) :=
    funext fun ω => vector_bilinear_apply_eq_sum (H ω) _ _
  rw [he, integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hip i j))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hip _ j)]
  simp_rw [integral_known_mul_increment_coordinates r t hrt _ (hc _ _) (hic _ _)]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [vectorBilinearTrace, integral_finsetSum Finset.univ (fun i _ => hic i i),
    Finset.mul_sum, mul_comm]

end FourPapersCommon
