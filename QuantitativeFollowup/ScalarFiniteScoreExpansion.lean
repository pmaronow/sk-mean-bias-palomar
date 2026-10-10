module
public import QuantitativeFollowup.ScalarGaussianScoreExpansion

@[expose] public section

/-! Actual terminal-spin score expansions for the finite scalar joint law.
All coefficients are the genuine potential gradient and curvature at the
retained atomic nodes, with zero weights and repeated nodes retained. -/
noncomputable section
open scoped BigOperators
namespace QuantitativeFollowup
open Paper SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

def scalarFiniteAtomIndex (i : Fin (k+1)) : Fin (k+3) := ⟨i+1,by omega⟩

def scalarFiniteAtomGradientScore (s : RSBScheme k) (β : ℝ)
    (x : QuantitativePaper.Field (k+3)) (i : Fin (k+1)) : ℝ :=
  (s.m (i+1)-s.m i)*Paper.parisiGradient β (Paper.parisiSchemeMeasure s)
    (FRSB.forwardSchemeTime s 1 (i+1),x (scalarFiniteAtomIndex i))

def scalarFiniteAtomHessianScore (s : RSBScheme k) (β : ℝ)
    (x : QuantitativePaper.Field (k+3)) (i : Fin (k+1)) : ℝ :=
  (s.m (i+1)-s.m i)*Paper.parisiHessian β (Paper.parisiSchemeMeasure s)
    (FRSB.forwardSchemeTime s 1 (i+1),x (scalarFiniteAtomIndex i))

theorem scalarFiniteEuclideanExponent_first_basis_score (s : RSBScheme k)
    (β : ℝ) (e : Bool) (x : QuantitativePaper.Field (k+3)) (j : Fin (k+3)) :
    fderiv ℝ (scalarFiniteEuclideanExponent s β e) x (EuclideanSpace.single j 1)=
      finiteCoordinateScore (Fin.last (k+2)) (Paper.spinSign e) scalarFiniteAtomIndex
        (scalarFiniteAtomGradientScore s β x) j := by
  rw [scalarFiniteEuclideanExponent_first]
  unfold finiteCoordinateScore scalarFiniteAtomGradientScore scalarFiniteAtomIndex
  simp only [PiLp.single_apply]
  congr 1
  · split_ifs <;> simp
  · exact Finset.sum_congr rfl fun i _=>by split_ifs <;> simp

theorem scalarFiniteEuclideanExponent_second_basis_score (s : RSBScheme k)
    (β : ℝ) (e : Bool) (x : QuantitativePaper.Field (k+3)) (j : Fin (k+3)) :
    vectorHessian (scalarFiniteEuclideanExponent s β e) x (EuclideanSpace.single j 1)
      (EuclideanSpace.single j 1)=
      finiteCoordinateScore (Fin.last (k+2)) 0 scalarFiniteAtomIndex
        (scalarFiniteAtomHessianScore s β x) j := by
  rw [scalarFiniteEuclideanExponent_second]
  unfold finiteCoordinateScore scalarFiniteAtomHessianScore scalarFiniteAtomIndex
  simp only [PiLp.single_apply,ite_self,zero_sub]
  congr 1
  exact Finset.sum_congr rfl fun i _=>by split_ifs <;> simp

theorem scalarFiniteGaussian_first_score_sum (s : RSBScheme k) (β : ℝ)
    (e : Bool) (x : QuantitativePaper.Field (k+3)) (f : Fin (k+3)→ℝ) :
    (∑j,f j*fderiv ℝ (scalarFiniteEuclideanExponent s β e) x (EuclideanSpace.single j 1))=
      Paper.spinSign e*f (Fin.last (k+2))-
        ∑i,scalarFiniteAtomGradientScore s β x i*f (scalarFiniteAtomIndex i) := by
  simp_rw [scalarFiniteEuclideanExponent_first_basis_score]
  exact finiteCoordinateScore_linear _ _ _ _ _

theorem scalarFiniteGaussian_diagonal_score_sum (s : RSBScheme k) (β : ℝ)
    (e : Bool) (x : QuantitativePaper.Field (k+3)) (f : Fin (k+3)→ℝ) :
    (∑j,f j*vectorHessian (scalarFiniteEuclideanExponent s β e) x
      (EuclideanSpace.single j 1) (EuclideanSpace.single j 1))=
      -(∑i,scalarFiniteAtomHessianScore s β x i*f (scalarFiniteAtomIndex i)) := by
  simp_rw [scalarFiniteEuclideanExponent_second_basis_score]
  simpa only [zero_mul,zero_sub] using finiteCoordinateScore_linear
    (Fin.last (k+2)) 0 scalarFiniteAtomIndex (scalarFiniteAtomHessianScore s β x) f

theorem scalarFiniteGaussian_quadratic_score_sum (s : RSBScheme k) (β : ℝ)
    (e : Bool) (x : QuantitativePaper.Field (k+3))
    (K : Fin (k+3)→Fin (k+3)→ℝ) (hK : ∀i j,K i j=K j i) :
    (∑i,∑j,K i j*fderiv ℝ (scalarFiniteEuclideanExponent s β e) x (EuclideanSpace.single i 1)*
      fderiv ℝ (scalarFiniteEuclideanExponent s β e) x (EuclideanSpace.single j 1))=
      K (Fin.last (k+2)) (Fin.last (k+2))-
        2*Paper.spinSign e*(∑i,scalarFiniteAtomGradientScore s β x i*K (scalarFiniteAtomIndex i) (Fin.last (k+2)))+
        ∑i,∑j,scalarFiniteAtomGradientScore s β x i*scalarFiniteAtomGradientScore s β x j*
          K (scalarFiniteAtomIndex i) (scalarFiniteAtomIndex j) := by
  simp_rw [scalarFiniteEuclideanExponent_first_basis_score]
  have he : Paper.spinSign e^2=1 := by cases e <;> norm_num [Paper.spinSign]
  simpa only [he,one_mul] using finiteCoordinateScore_quadratic (Fin.last (k+2))
    (Paper.spinSign e) scalarFiniteAtomIndex (scalarFiniteAtomGradientScore s β x) K hK

end QuantitativeFollowup
