module
public import QuantitativePaper.VectorMeasureCovarianceMatrix

@[expose] public section

/-! Exact finite matrix expansion of the conditional two-replica defect. -/
noncomputable section
open scoped BigOperators
namespace QuantitativePaper
variable {n : ℕ}

theorem symmetric_matrix_square_trace (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : ∀i j,C i j=C j i) :
    Matrix.trace (C*C)=∑i : Fin n,∑j : Fin n,(C i j)^2 := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [←hC i j,pow_two]

theorem spin_matrix_second_moment_expansion (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : ∀i j,C i j=C j i) (M : Fin n→ℝ) :
    (∑i : Fin n,∑j : Fin n,(C i j+M i*M j)^2)=
      Matrix.trace (C*C)+2*(∑i : Fin n,∑j : Fin n,C i j*M i*M j)+
        (∑i : Fin n,(M i)^2)^2 := by
  have he : (∑i : Fin n,∑j : Fin n,(C i j+M i*M j)^2)=
      ∑i : Fin n,∑j : Fin n,((C i j)^2+2*(C i j*M i*M j)+(M i)^2*(M j)^2) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hp : (∑i : Fin n,∑j : Fin n,(M i)^2*(M j)^2)=(∑i : Fin n,(M i)^2)^2 := by
    rw [pow_two,Finset.sum_mul]
    simp only [Finset.mul_sum]
  have hc : (∑i : Fin n,∑j : Fin n,2*(C i j*M i*M j))=
      2*(∑i : Fin n,∑j : Fin n,C i j*M i*M j) := by
    simp only [Finset.mul_sum]
  rw [he]
  simp only [Finset.sum_add_distrib]
  rw [hc,hp,symmetric_matrix_square_trace C hC]

theorem spin_matrix_defect_expansion (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : ∀i j,C i j=C j i) (M : Fin n→ℝ) (q c : ℝ) :
    c^2*(∑i : Fin n,∑j : Fin n,(C i j+M i*M j)^2)-
      2*q*(c*∑i : Fin n,(M i)^2)+q^2=
    c^2*Matrix.trace (C*C)+2*c^2*(∑i : Fin n,∑j : Fin n,C i j*M i*M j)+
      (c*(∑i : Fin n,(M i)^2)-q)^2 := by
  rw [spin_matrix_second_moment_expansion C hC M]
  ring

end QuantitativePaper
