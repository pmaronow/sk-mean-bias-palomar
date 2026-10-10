module
public import QuantitativePaper.GOECompletion

@[expose] public section

/-! The literal half-quadratic GOE Hamiltonian equals the triangular SK
Hamiltonian plus the genuine half-trace diagonal completion. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativePaper

private theorem triple_sum_rotate {ι κ ζ : Type*} [Fintype ι] [Fintype κ] [Fintype ζ]
    (f : ι → κ → ζ → ℝ) : (∑ i,∑ j,∑ k,f i j k) = ∑ k,∑ i,∑ j,f i j k := by
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset ι)) (t := (Finset.univ : Finset ζ))]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  exact Finset.sum_comm

private theorem quadratic_sum_add {n : ℕ} (v : Fin n → ℝ)
    (M D : Fin n → Fin n → ℝ) :
    (∑ i,∑ j,v i*(M i j+D i j)*v j) =
      (∑ i,∑ j,v i*M i j*v j)+(∑ i,∑ j,v i*D i j*v j) := by
  simp only [mul_add,add_mul,Finset.sum_add_distrib]

theorem goeMatrix_quadratic (n : ℕ) (p : GOEDisorder n) (v : Fin n → ℝ) :
    (∑ i,∑ j,v i*goeMatrix n p i j*v j) =
      2*(∑ e : Edge n,(p.1 e/Real.sqrt (n : ℝ))*v e.val.1*v e.val.2)+
      Real.sqrt (2/(n : ℝ))*(∑ i,p.2 i*v i^2) := by
  have hoff (e : Edge n) : (∑ i : Fin n,∑ j : Fin n,
      v i*((p.1 e/Real.sqrt (n : ℝ))*
        ((if i = e.val.1 then 1 else 0)*(if j = e.val.2 then 1 else 0)+
         (if i = e.val.2 then 1 else 0)*(if j = e.val.1 then 1 else 0)))*v j) =
      2*((p.1 e/Real.sqrt (n : ℝ))*v e.val.1*v e.val.2) := by
    simp [mul_add,add_mul,Finset.sum_add_distrib,mul_ite,ite_mul]
    ring
  have hdiag : (∑ i : Fin n,∑ j : Fin n,
      v i*(if i = j then Real.sqrt (2/(n : ℝ))*p.2 i else 0)*v j) =
      Real.sqrt (2/(n : ℝ))*(∑ i,p.2 i*v i^2) := by
    simp only [mul_ite,ite_mul,mul_zero,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold goeMatrix
  rw [quadratic_sum_add,hdiag]
  simp only [add_left_inj]
  simp_rw [Finset.mul_sum,Finset.sum_mul]
  rw [triple_sum_rotate]
  simp_rw [hoff]

theorem goeMatrix_energy (n : ℕ) (hn : 0 < n) (p : GOEDisorder n) (σ : Configuration n) :
    (1/2 : ℝ)*(∑ i,∑ j,Paper.spinSign (σ i)*goeMatrix n p i j*Paper.spinSign (σ j)) =
      energy n p.1 σ+goeDiagonalNoise n p.2 := by
  have hedge : (∑ e : Edge n,(p.1 e/Real.sqrt (n : ℝ))*
      Paper.spinSign (σ e.val.1)*Paper.spinSign (σ e.val.2)) = energy n p.1 σ := by
    unfold energy Paper.skHamiltonian
    simp only [zero_mul,add_zero]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  have hnoise := goeMatrix_half_trace n hn p
  unfold Matrix.trace Matrix.diag at hnoise
  simp_rw [goeMatrix_diagonal] at hnoise
  rw [← Finset.mul_sum,← mul_assoc] at hnoise
  rw [goeMatrix_quadratic]
  simp_rw [Paper.spinSign_sq]
  simp only [mul_one]
  rw [hedge,← hnoise]
  ring

end QuantitativePaper
