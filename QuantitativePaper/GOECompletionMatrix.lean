module
public import QuantitativePaper.VectorGaussianDiagonalShift
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

/-! The literal GOE matrix completion of triangular SK, including the
half-trace diagonal variable and actual matrix/spin partition identities. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1000000

def goeUpperMatrix (n : ℕ) (g : Couplings n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if h : i<j then g ⟨(i,j),h⟩/Real.sqrt (n : ℝ) else 0

def goeCompletionMatrix (n : ℕ) (p : Couplings n×(Fin n→ℝ)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => goeUpperMatrix n p.1 i j+goeUpperMatrix n p.1 j i+
    if i=j then Real.sqrt (2/(n : ℝ))*p.2 i else 0

def goeDiagonalTrace (n : ℕ) (p : Couplings n×(Fin n→ℝ)) : ℝ :=
  Matrix.trace (goeCompletionMatrix n p)/2

def goeSpinQuadratic (n : ℕ) (p : Couplings n×(Fin n→ℝ)) (σ : Configuration n) : ℝ :=
  (∑i,∑j,goeCompletionMatrix n p i j*Paper.spinSign (σ i)*Paper.spinSign (σ j))/2

theorem goeCompletionMatrix_symmetric (n : ℕ) (p : Couplings n×(Fin n→ℝ)) :
    (goeCompletionMatrix n p).IsSymm := by
  change (goeCompletionMatrix n p).transpose=goeCompletionMatrix n p
  ext i j
  change goeCompletionMatrix n p j i=goeCompletionMatrix n p i j
  unfold goeCompletionMatrix
  by_cases h : i=j
  · subst j; rfl
  · simp only [Matrix.transpose_apply,h,Ne.symm h,ite_false,add_zero]
    ring

theorem goeCompletionMatrix_diagonal (n : ℕ) (p : Couplings n×(Fin n→ℝ)) (i : Fin n) :
    goeCompletionMatrix n p i i=Real.sqrt (2/(n : ℝ))*p.2 i := by
  simp [goeCompletionMatrix,goeUpperMatrix]

theorem goeCompletionMatrix_upper (n : ℕ) (p : Couplings n×(Fin n→ℝ))
    (i j : Fin n) (h : i<j) :
    goeCompletionMatrix n p i j=p.1 ⟨(i,j),h⟩/Real.sqrt (n : ℝ) := by
  simp [goeCompletionMatrix,goeUpperMatrix,h,not_lt.mpr h.le,ne_of_lt h]

theorem goeDiagonalTrace_eq (n : ℕ) (p : Couplings n×(Fin n→ℝ)) :
    goeDiagonalTrace n p=Real.sqrt (2/(n : ℝ))/2*(∑i,p.2 i) := by
  simp only [goeDiagonalTrace,Matrix.trace,Matrix.diag,goeCompletionMatrix_diagonal,←Finset.mul_sum]
  ring

private theorem goeUpper_spin_sum (n : ℕ) (g : Couplings n) (σ : Configuration n) :
    (∑i : Fin n,∑j : Fin n,goeUpperMatrix n g i j*Paper.spinSign (σ i)*Paper.spinSign (σ j)) =
      energy n g σ := by
  classical
  rw [←Finset.sum_product',Finset.univ_product_univ]
  let f : (Fin n×Fin n)→ℝ := fun ij=>
    goeUpperMatrix n g ij.1 ij.2*Paper.spinSign (σ ij.1)*Paper.spinSign (σ ij.2)
  have he : (∑ij : Fin n×Fin n,f ij) =
      ∑e : Edge n,g e/Real.sqrt (n : ℝ)*Paper.spinSign (σ e.val.1)*Paper.spinSign (σ e.val.2) := by
    calc
      _ = ∑ij∈Finset.univ.filter (fun ij : Fin n×Fin n=>ij.1 < ij.2),f ij := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro ij _ hnot
        have hh : ¬(ij.1 < ij.2) := by simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hnot
        simp [f,goeUpperMatrix,hh]
      _ = ∑e : Edge n,f e.val := by
        exact Finset.sum_subtype (Finset.univ.filter (fun ij : Fin n×Fin n=>ij.1 < ij.2))
          (by simp) f
      _ = _ := by
        apply Finset.sum_congr rfl
        intro e _
        simp only [f,goeUpperMatrix,dif_pos e.property]
  change (∑ij : Fin n×Fin n,f ij)=_
  rw [he]
  unfold energy Paper.skHamiltonian
  simp only [zero_mul,add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem goeSpinQuadratic_eq_completed_energy (n : ℕ)
    (p : Couplings n×(Fin n→ℝ)) (σ : Configuration n) :
    goeSpinQuadratic n p σ=energy n p.1 σ+goeDiagonalTrace n p := by
  classical
  have hswap : (∑i : Fin n,∑j : Fin n,
      goeUpperMatrix n p.1 j i*Paper.spinSign (σ i)*Paper.spinSign (σ j)) =
      ∑i : Fin n,∑j : Fin n,
        goeUpperMatrix n p.1 i j*Paper.spinSign (σ i)*Paper.spinSign (σ j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hdiag : (∑i : Fin n,∑j : Fin n,
      (if i=j then Real.sqrt (2/(n : ℝ))*p.2 i else 0)*
        Paper.spinSign (σ i)*Paper.spinSign (σ j)) =
      ∑i : Fin n,Real.sqrt (2/(n : ℝ))*p.2 i := by
    simp only [ite_mul,mul_zero,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = (Real.sqrt (2/(n : ℝ))*p.2 i)*Paper.spinSign (σ i)^2 := by ring
      _ = _ := by rw [Paper.spinSign_sq,mul_one]
  unfold goeSpinQuadratic
  simp only [goeCompletionMatrix,add_mul,Finset.sum_add_distrib]
  rw [hswap,hdiag,goeUpper_spin_sum,goeDiagonalTrace_eq,←Finset.mul_sum]
  ring

def goeCompletedLogPartition (n : ℕ) (β : ℝ) (p : Couplings n×(Fin n→ℝ)) : ℝ :=
  Real.log (∑σ : Configuration n,Real.exp (β*goeSpinQuadratic n p σ))

theorem goeCompletedLogPartition_eq (n : ℕ) (β : ℝ) (p : Couplings n×(Fin n→ℝ)) :
    goeCompletedLogPartition n β p=logPartition n β p.1+β*goeDiagonalTrace n p := by
  simp only [goeCompletedLogPartition,goeSpinQuadratic_eq_completed_energy,mul_add,Real.exp_add]
  rw [←Finset.sum_mul,Real.log_mul]
  · rw [Real.log_exp]
    congr 1
    unfold logPartition Paper.skPartitionFunction
    simp_rw [energy_parameter]
  · exact Finset.sum_pos (fun σ _=>Real.exp_pos _) Finset.univ_nonempty |>.ne'
  · exact Real.exp_ne_zero _

def goeGroundState (n : ℕ) (p : Couplings n×(Fin n→ℝ)) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (goeSpinQuadratic n p)

theorem goeGroundState_eq (n : ℕ) (p : Couplings n×(Fin n→ℝ)) :
    goeGroundState n p=groundState n p.1+goeDiagonalTrace n p := by
  unfold goeGroundState groundState
  simp only [goeSpinQuadratic_eq_completed_energy]
  apply le_antisymm
  · apply Finset.sup'_le
    intro σ _
    exact add_le_add (Finset.le_sup' (s:=Finset.univ)
      (f:=energy n p.1) (Finset.mem_univ σ)) le_rfl
  · obtain ⟨σ,hσ,hmax⟩ := Finset.exists_mem_eq_sup'
      (Finset.univ_nonempty : (Finset.univ : Finset (Configuration n)).Nonempty)
      (energy n p.1)
    rw [hmax]
    exact Finset.le_sup' (fun x=>energy n p.1 x+goeDiagonalTrace n p) hσ

end QuantitativePaper
