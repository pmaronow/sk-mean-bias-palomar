module
public import QuantitativeFollowup.ScalarScoreContractionAlgebra
public import QuantitativeFollowup.ScalarFiniteObservableDerivatives

@[expose] public section

/-! The sparse score contraction instantiated with the actual retained scalar
PDE observable and density. Diagonality is proved from the genuine spatial
Hessian, rather than supplied as a Gaussian response assumption. -/
noncomputable section
open Set
open scoped BigOperators NNReal ContDiff
namespace QuantitativeFollowup
open Paper SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
variable {k : ℕ}

theorem scalarFiniteEuclideanExponent_second_basis (s : RSBScheme k) (β : ℝ)
    (e : Bool) (x : QuantitativePaper.Field (k+3)) (i j : Fin (k+3)) :
    vectorHessian (scalarFiniteEuclideanExponent s β e) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)=
      if i=j then vectorHessian (scalarFiniteEuclideanExponent s β e) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) else 0 := by
  by_cases hij : i=j
  · simp [hij]
  · rw [if_neg hij,scalarFiniteEuclideanExponent_second]
    rw [Finset.sum_eq_zero]
    · simp
    · intro l _
      by_cases hi : (⟨l+1,by omega⟩ : Fin (k+3))=i
      · have hj : (⟨l+1,by omega⟩ : Fin (k+3))≠j := by simpa [hi] using hij
        simp [PiLp.single_apply,hi,hij]
      · simp [PiLp.single_apply,hi]

theorem scalarFiniteGaussianScore_basis (s : RSBScheme k) (β : ℝ) (e : Bool)
    (p : Fin (k+3)) (x : QuantitativePaper.Field (k+3)) (c : ℝ) (i j : Fin (k+3)) :
    gaussianScoreBilinear (scalarFiniteEuclideanExponent s β e) (scalarFiniteGradientSquare s β p)
      x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) c=
      scalarSparseGaussianScore p
        (fun l=>fderiv ℝ (scalarFiniteEuclideanExponent s β e) x (EuclideanSpace.single l 1))
        (fun l=>vectorHessian (scalarFiniteEuclideanExponent s β e) x
          (EuclideanSpace.single l 1) (EuclideanSpace.single l 1))
        (2*Paper.parisiGradient β (Paper.parisiSchemeMeasure s) (FRSB.forwardSchemeTime s 1 p,x p)*
          Paper.parisiHessian β (Paper.parisiSchemeMeasure s) (FRSB.forwardSchemeTime s 1 p,x p))
        (2*Paper.parisiHessian β (Paper.parisiSchemeMeasure s) (FRSB.forwardSchemeTime s 1 p,x p)^2+
          2*Paper.parisiGradient β (Paper.parisiSchemeMeasure s) (FRSB.forwardSchemeTime s 1 p,x p)*
            FRSB.parisiSpatialJet β (Paper.parisiSchemeMeasure s) 3 (FRSB.forwardSchemeTime s 1 p) (x p))
        (scalarFiniteGradientSquare s β p x-c) i j := by
  unfold gaussianScoreBilinear scalarSparseGaussianScore
  rw [scalarFiniteGradientSquare_first,scalarFiniteGradientSquare_first,
    scalarFiniteGradientSquare_second,scalarFiniteEuclideanExponent_second_basis]
  simp only [PiLp.single_apply]
  have hpi : (p=i) ↔ (i=p) := eq_comm
  have hpj : (p=j) ↔ (j=p) := eq_comm
  simp only [hpi,hpj]
  by_cases hip : i=p <;> by_cases hjp : j=p <;>
    simp [hip,hjp] <;> ring

theorem scalarFiniteGaussianScore_contraction (s : RSBScheme k) (β : ℝ) (e : Bool)
    (p : Fin (k+3)) (x : QuantitativePaper.Field (k+3)) (c : ℝ)
    (K : Fin (k+3)→Fin (k+3)→ℝ) (hK : ∀i j,K i j=K j i) :
    (1/2:ℝ)*(∑i,∑j,K i j*gaussianScoreBilinear (scalarFiniteEuclideanExponent s β e)
      (scalarFiniteGradientSquare s β p) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) c)=
      (1/2:ℝ)*K p p*(2*Paper.parisiHessian β (Paper.parisiSchemeMeasure s)
          (FRSB.forwardSchemeTime s 1 p,x p)^2+
        2*Paper.parisiGradient β (Paper.parisiSchemeMeasure s) (FRSB.forwardSchemeTime s 1 p,x p)*
          FRSB.parisiSpatialJet β (Paper.parisiSchemeMeasure s) 3 (FRSB.forwardSchemeTime s 1 p) (x p))+
      (2*Paper.parisiGradient β (Paper.parisiSchemeMeasure s) (FRSB.forwardSchemeTime s 1 p,x p)*
        Paper.parisiHessian β (Paper.parisiSchemeMeasure s) (FRSB.forwardSchemeTime s 1 p,x p))*
        (∑i,K i p*fderiv ℝ (scalarFiniteEuclideanExponent s β e) x (EuclideanSpace.single i 1))+
      (1/2:ℝ)*(scalarFiniteGradientSquare s β p x-c)*
        ((∑i,K i i*vectorHessian (scalarFiniteEuclideanExponent s β e) x
            (EuclideanSpace.single i 1) (EuclideanSpace.single i 1))+
          (∑i,∑j,K i j*fderiv ℝ (scalarFiniteEuclideanExponent s β e) x (EuclideanSpace.single i 1)*
            fderiv ℝ (scalarFiniteEuclideanExponent s β e) x (EuclideanSpace.single j 1))) := by
  simp_rw [scalarFiniteGaussianScore_basis]
  exact scalar_sparse_score_contraction p K hK _ _ _ _ _

end QuantitativeFollowup
