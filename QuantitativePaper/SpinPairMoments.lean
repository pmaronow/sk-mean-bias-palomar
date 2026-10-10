module
public import QuantitativePaper.CompletionCovariance
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Exact overlap moments of two independent samples from a genuine finite
spin law. These are identities of actual probability integrals, not symbolic
replica expectations. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1200000
variable {n : ℕ}

theorem integral_overlap_spin_product (P : Measure (Configuration n))
    [IsProbabilityMeasure P] :
    (∫z,overlap n z.1 z.2∂P.prod P)=
      (1/(n:ℝ))*∑i : Fin n,(∫σ,Paper.spinSign (σ i)∂P)^2 := by
  unfold overlap
  rw [integral_const_mul,integral_finsetSum _ (fun _ _=>Integrable.of_finite)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_prod_mul (fun σ : Configuration n=>Paper.spinSign (σ i))
    (fun τ : Configuration n=>Paper.spinSign (τ i))]
  ring

theorem overlap_square_spin_sum (σ τ : Configuration n) :
    overlap n σ τ^2=(1/(n:ℝ))^2*
      ∑i : Fin n,∑j : Fin n,
        (Paper.spinSign (σ i)*Paper.spinSign (σ j))*
          (Paper.spinSign (τ i)*Paper.spinSign (τ j)) := by
  unfold overlap
  rw [mul_pow]
  simp only [pow_two]
  rw [Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem integral_overlap_square_spin_product (P : Measure (Configuration n))
    [IsProbabilityMeasure P] :
    (∫z,overlap n z.1 z.2^2∂P.prod P)=
      (1/(n:ℝ))^2*∑i : Fin n,∑j : Fin n,
        (∫σ,Paper.spinSign (σ i)*Paper.spinSign (σ j)∂P)^2 := by
  simp_rw [overlap_square_spin_sum]
  rw [integral_const_mul,integral_finsetSum _ (fun _ _=>Integrable.of_finite)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun _ _=>Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_prod_mul
    (fun σ : Configuration n=>Paper.spinSign (σ i)*Paper.spinSign (σ j))
    (fun τ : Configuration n=>Paper.spinSign (τ i)*Paper.spinSign (τ j))]
  ring

theorem integral_overlap_defect_spin_product (P : Measure (Configuration n))
    [IsProbabilityMeasure P] (q : ℝ) :
    (∫z,(overlap n z.1 z.2-q)^2∂P.prod P)=
      (1/(n:ℝ))^2*∑i : Fin n,∑j : Fin n,
        (∫σ,Paper.spinSign (σ i)*Paper.spinSign (σ j)∂P)^2-
      2*q*((1/(n:ℝ))*∑i : Fin n,(∫σ,Paper.spinSign (σ i)∂P)^2)+q^2 := by
  have he : (fun z : Configuration n×Configuration n=>(overlap n z.1 z.2-q)^2)=
      fun z=>overlap n z.1 z.2^2-2*q*overlap n z.1 z.2+q^2 := by
    funext z
    ring
  rw [he,integral_add Integrable.of_finite (integrable_const _),
    integral_sub Integrable.of_finite Integrable.of_finite,integral_const_mul,
    integral_overlap_spin_product,integral_overlap_square_spin_product]
  simp

end QuantitativePaper
