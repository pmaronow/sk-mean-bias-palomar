module
public import QuantitativePaper.VectorTiltedIncrementMoments
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-! Exact one-step L² isometry for any square-integrable linear coefficient
known in the full vector Wiener past, under the actual fractional tilt. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

theorem vector_linear_apply_square_eq_sum (L : Field n →L[ℝ] ℝ) (z : Field n) :
    (L z)^2 = ∑ i : Fin n, ∑ j : Fin n,
      (L (EuclideanSpace.single i 1)*L (EuclideanSpace.single j 1))*(z i*z j) := by
  rw [pow_two, vector_linear_apply_eq_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem integrable_tilted_known_CLM_increment_sq (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t ≤ 1) (r u : ℝ≥0) (hru : r ≤ u)
    (L : VectorDisorderBrownianSample n → (Field n →L[ℝ] ℝ))
    (hL : Measurable[vectorBrownianFiltration n r] L)
    (hL2 : MemLp L 2 (vectorMeasureDisorderTilt μ β t a)) :
    Integrable (fun sample => (L sample (disorderVectorBrownianIncrement r u sample))^2)
      (vectorMeasureDisorderTilt μ β t a) := by
  have hE (i : Fin n) : MemLp (fun sample => L sample (EuclideanSpace.single i 1)) 2
      (vectorMeasureDisorderTilt μ β t a) :=
    hL2.continuousLinearMap_comp ((ContinuousLinearMap.apply ℝ ℝ) (EuclideanSpace.single i 1))
  have hZ (i j : Fin n) : Measurable[vectorBrownianFiltration n r]
      (fun sample => L sample (EuclideanSpace.single i 1)*L sample (EuclideanSpace.single j 1)) :=
    (((ContinuousLinearMap.apply ℝ ℝ) (EuclideanSpace.single i 1)).continuous.measurable.comp hL).mul
      (((ContinuousLinearMap.apply ℝ ℝ) (EuclideanSpace.single j 1)).continuous.measurable.comp hL)
  simp_rw [vector_linear_apply_square_eq_sum]
  apply integrable_finsetSum Finset.univ
  intro i _
  apply integrable_finsetSum Finset.univ
  intro j _
  exact integrable_tilted_known_mul_increment_coordinates μ β t a ht r u hru _ (hZ i j)
    (memLp_one_iff_integrable.mp ((hE i).mul (hE j))) i j

theorem memLp_tilted_known_CLM_increment (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t ≤ 1) (r u : ℝ≥0) (hru : r ≤ u)
    (L : VectorDisorderBrownianSample n → (Field n →L[ℝ] ℝ))
    (hL : Measurable[vectorBrownianFiltration n r] L)
    (hL2 : MemLp L 2 (vectorMeasureDisorderTilt μ β t a)) :
    MemLp (fun sample => L sample (disorderVectorBrownianIncrement r u sample)) 2
      (vectorMeasureDisorderTilt μ β t a) := by
  have hc : Continuous (fun p : (Field n →L[ℝ] ℝ) × Field n => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hm := hc.comp_aestronglyMeasurable (hL2.aestronglyMeasurable.prodMk
    (measurable_disorderVectorBrownianIncrement r u).aestronglyMeasurable)
  apply (memLp_two_iff_integrable_sq hm).mpr
  exact integrable_tilted_known_CLM_increment_sq μ β t a ht r u hru L hL hL2

theorem integral_tilted_known_CLM_increment_sq (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t ≤ 1) (r u : ℝ≥0) (hru : r ≤ u)
    (L : VectorDisorderBrownianSample n → (Field n →L[ℝ] ℝ))
    (hL : Measurable[vectorBrownianFiltration n r] L)
    (hL2 : MemLp L 2 (vectorMeasureDisorderTilt μ β t a)) :
    (∫ sample, (L sample (disorderVectorBrownianIncrement r u sample))^2
      ∂vectorMeasureDisorderTilt μ β t a) = ((u : ℝ)-r)*
        ∫ sample, (∑ i : Fin n, (L sample (EuclideanSpace.single i 1))^2)
          ∂vectorMeasureDisorderTilt μ β t a := by
  have hE (i : Fin n) : MemLp (fun sample => L sample (EuclideanSpace.single i 1)) 2
      (vectorMeasureDisorderTilt μ β t a) :=
    hL2.continuousLinearMap_comp ((ContinuousLinearMap.apply ℝ ℝ) (EuclideanSpace.single i 1))
  have hZ (i j : Fin n) : Measurable[vectorBrownianFiltration n r]
      (fun sample => L sample (EuclideanSpace.single i 1)*L sample (EuclideanSpace.single j 1)) :=
    (((ContinuousLinearMap.apply ℝ ℝ) (EuclideanSpace.single i 1)).continuous.measurable.comp hL).mul
      (((ContinuousLinearMap.apply ℝ ℝ) (EuclideanSpace.single j 1)).continuous.measurable.comp hL)
  have hiZ (i j : Fin n) : Integrable
      (fun sample => L sample (EuclideanSpace.single i 1)*L sample (EuclideanSpace.single j 1))
      (vectorMeasureDisorderTilt μ β t a) :=
    memLp_one_iff_integrable.mp ((hE i).mul (hE j))
  have hip (i j : Fin n) := integrable_tilted_known_mul_increment_coordinates
    μ β t a ht r u hru _ (hZ i j) (hiZ i j) i j
  have he : (fun sample => (L sample (disorderVectorBrownianIncrement r u sample))^2) =
      (fun sample => ∑ i : Fin n, ∑ j : Fin n,
        (L sample (EuclideanSpace.single i 1)*L sample (EuclideanSpace.single j 1))*
          (disorderVectorBrownianIncrement r u sample i*disorderVectorBrownianIncrement r u sample j)) :=
    funext fun sample => vector_linear_apply_square_eq_sum (L sample) _
  rw [he]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hip i j))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hip _ j),
    integral_tilted_known_mul_increment_coordinates μ β t a ht r u hru _ (hZ _ _) (hiZ _ _)]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [integral_finsetSum Finset.univ (fun i _ => by simpa only [pow_two] using hiZ i i)]
  simp only [Finset.mul_sum, pow_two, mul_comm]

end QuantitativePaper
