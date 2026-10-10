module
public import QuantitativeFollowup.ScalarTransportHeatData
public import QuantitativeFollowup.ScalarFiniteScoreContraction
public import QuantitativeFollowup.ScalarFiniteScoreExpansion

@[expose] public section

/-! The genuine Gaussian covariance direction and sparse spatial score of
the transported scalar family, including repeated zero-variance cells. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BigOperators ContDiff
namespace QuantitativeFollowup
open Paper SpinGlass.Targets FourPapersCommon QuantitativePaper
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

def scalarTransportCovarianceLevel (s : RSBScheme k) (φ : C(Paper.Overlap,ℝ))
    (i j : Fin (k+3)) : ℝ := φ (scalarSchemeTransportNode s (min (i:ℕ) (j:ℕ)))

theorem scalarTransportCovarianceLevel_symm (s : RSBScheme k)
    (φ : C(Paper.Overlap,ℝ)) (i j : Fin (k+3)) :
    scalarTransportCovarianceLevel s φ i j=scalarTransportCovarianceLevel s φ j i := by
  simp only [scalarTransportCovarianceLevel,min_comm]

theorem scalarTransportCovarianceLevel_self (s : RSBScheme k)
    (φ : C(Paper.Overlap,ℝ)) (i : Fin (k+3)) :
    scalarTransportCovarianceLevel s φ i i=φ (scalarSchemeTransportNode s i) := by
  simp only [scalarTransportCovarianceLevel,min_self]

theorem scalarTransportCovarianceLevel_last (s : RSBScheme k)
    (φ : C(Paper.Overlap,ℝ)) (i : Fin (k+3)) :
    scalarTransportCovarianceLevel s φ i (Fin.last (k+2))=φ (scalarSchemeTransportNode s i) := by
  unfold scalarTransportCovarianceLevel
  rw [min_eq_left (by have:=i.isLt; simp only [Fin.val_last];omega)]

theorem scalarTransportCovarianceLevel_terminal (s : RSBScheme k)
    (φ : C(Paper.Overlap,ℝ)) (h1 : φ 1=0) :
    scalarTransportCovarianceLevel s φ (Fin.last (k+2)) (Fin.last (k+2))=0 := by
  rw [scalarTransportCovarianceLevel_self]
  have he : scalarSchemeTransportNode s (Fin.last (k+2))=(1:Paper.Overlap) := by
    apply Subtype.ext
    rw [scalarSchemeTransportNode_coe _ _ (by simp [Fin.val_last])]
    exact s.q_top
  rw [he,h1]

theorem scalarTransportGaussianDirection_zero (s : RSBScheme k) (β : ℝ)
    (hβ : β≠0) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (i j : Fin (k+3)) :
    gaussianLinearCovarianceDirection
      (scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficient s β φ 0) (k+2))
      (scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficientDerivative s β φ 0) (k+2)) i j=
      β^2*scalarTransportCovarianceLevel s φ i j := by
  have hd:=hasDerivAt_gaussianLinearCovariance
    (fun u=>scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficient s β φ u) (k+2))
    (scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficientDerivative s β φ 0) (k+2)) 0
    (hasDerivAt_scalarTransportGaussianHistory s β hβ φ L hφ h0 h1 0 (by simp)) i j
  exact hd.unique (hasDerivAt_scalarTransportGaussianCovariance s β φ L hφ h0 h1 i j)

theorem scalarSchemeTransportNode_eq_clock (s : RSBScheme k) (i : ℕ) (hi : i≤k+2) :
    (scalarSchemeTransportNode s i:ℝ)=FRSB.forwardSchemeTime s 1 i := by
  rw [scalarSchemeTransportNode_coe s i hi,scalarSchemeHistoryClock_coe s i hi]

theorem scalarTransportExponent_zero (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (e : Bool) :
    scalarTransportEuclideanExponent s β φ e 0=scalarFiniteEuclideanExponent s β e := by
  funext x
  unfold scalarTransportEuclideanExponent scalarFiniteEuclideanExponent scalarTransportNodePotential
  simp only [scalarTransportMeasure_zero,scalarLevelTransport_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [scalarSchemeTransportNode_eq_clock s (i+1) (by omega)]

theorem scalarTransportSquare_zero (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (p : Fin (k+3)) :
    scalarTransportGradientSquare s β φ p 0=scalarFiniteGradientSquare s β p := by
  funext x
  unfold scalarTransportGradientSquare scalarTransportNodeGradient scalarFiniteGradientSquare
  rw [scalarTransportMeasure_zero,scalarLevelTransport_zero,
    scalarSchemeTransportNode_eq_clock s p (by omega)]

theorem scalarTransport_score_covariance_contraction (s : RSBScheme k) (β : ℝ)
    (hβ : β≠0) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (e : Bool) (p : Fin (k+3)) (x : QuantitativePaper.Field (k+3)) (center : ℝ) :
    (∑i : Fin (k+2),gaussianScoreBilinear (scalarTransportEuclideanExponent s β φ e 0)
      (scalarTransportGradientSquare s β φ p 0) x
      (scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficient s β φ 0) (k+2)
        (EuclideanSpace.single i 1))
      (scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficientDerivative s β φ 0) (k+2)
        (EuclideanSpace.single i 1)) center)=
    β^2*((1/2:ℝ)*∑i : Fin (k+3),∑j : Fin (k+3),scalarTransportCovarianceLevel s φ i j*
      gaussianScoreBilinear (scalarFiniteEuclideanExponent s β e) (scalarFiniteGradientSquare s β p)
        x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) center) := by
  rw [scalarTransportExponent_zero,scalarTransportSquare_zero]
  rw [gaussian_covariance_score_contraction _ _
    ((contDiff_scalarFiniteEuclideanExponent s β e).of_le (by simp))
    ((contDiff_scalarFiniteGradientSquare s β p).of_le (by simp))]
  simp_rw [scalarTransportGaussianDirection_zero s β hβ φ L hφ h0 h1]
  simp only [mul_assoc,←Finset.mul_sum]
  ring

theorem scalarTransport_score_expansion (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (h1 : φ 1=0) (e : Bool) (p : Fin (k+3))
    (x : QuantitativePaper.Field (k+3)) (center : ℝ) :
    (1/2:ℝ)*(∑i : Fin (k+3),∑j : Fin (k+3),scalarTransportCovarianceLevel s φ i j*
      gaussianScoreBilinear (scalarFiniteEuclideanExponent s β e) (scalarFiniteGradientSquare s β p)
        x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) center)=
    (1/2:ℝ)*φ (scalarSchemeTransportNode s p)*
      (2*Paper.parisiHessian β (Paper.parisiSchemeMeasure s) (FRSB.forwardSchemeTime s 1 p,x p)^2+
        2*Paper.parisiGradient β (Paper.parisiSchemeMeasure s) (FRSB.forwardSchemeTime s 1 p,x p)*
          FRSB.parisiSpatialJet β (Paper.parisiSchemeMeasure s) 3 (FRSB.forwardSchemeTime s 1 p) (x p))+
    (2*Paper.parisiGradient β (Paper.parisiSchemeMeasure s) (FRSB.forwardSchemeTime s 1 p,x p)*
      Paper.parisiHessian β (Paper.parisiSchemeMeasure s) (FRSB.forwardSchemeTime s 1 p,x p))*
      (Paper.spinSign e*φ (scalarSchemeTransportNode s p)-
        ∑i,scalarFiniteAtomGradientScore s β x i*scalarTransportCovarianceLevel s φ (scalarFiniteAtomIndex i) p)+
    (1/2:ℝ)*(scalarFiniteGradientSquare s β p x-center)*(
      -(∑i,scalarFiniteAtomHessianScore s β x i*φ (scalarSchemeTransportNode s (scalarFiniteAtomIndex i)))
      -2*Paper.spinSign e*(∑i,scalarFiniteAtomGradientScore s β x i*φ (scalarSchemeTransportNode s (scalarFiniteAtomIndex i)))+
      ∑i,∑j,scalarFiniteAtomGradientScore s β x i*scalarFiniteAtomGradientScore s β x j*
        scalarTransportCovarianceLevel s φ (scalarFiniteAtomIndex i) (scalarFiniteAtomIndex j)) := by
  rw [scalarFiniteGaussianScore_contraction s β e p x center _
    (scalarTransportCovarianceLevel_symm s φ),
    scalarFiniteGaussian_first_score_sum,scalarFiniteGaussian_diagonal_score_sum,
    scalarFiniteGaussian_quadratic_score_sum _ _ _ _ _ (scalarTransportCovarianceLevel_symm s φ)]
  simp_rw [scalarTransportCovarianceLevel_terminal s φ h1,scalarTransportCovarianceLevel_self,
    scalarTransportCovarianceLevel_last]
  rw [scalarTransportCovarianceLevel_symm s φ (Fin.last (k+2)) p,
    scalarTransportCovarianceLevel_last]
  ring

end QuantitativeFollowup
