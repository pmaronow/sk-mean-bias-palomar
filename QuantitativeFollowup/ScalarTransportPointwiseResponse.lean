module
public import QuantitativeFollowup.ScalarTransportGaussianResponse
public import QuantitativeFollowup.ScalarTransportScoreContraction
public import QuantitativeFollowup.ScalarSevenTermCancellation

@[expose] public section

/-! Exact pointwise reduction of the genuine Gaussian transport score to
the seven response terms and one centered terminal-spin term. No stochastic
conditioning or response identity is used in this algebraic reduction. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
open Paper SpinGlass.Targets FourPapersCommon QuantitativePaper
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

def scalarFiniteNodeGradient (s : RSBScheme k) (β : ℝ) (x : QuantitativePaper.Field (k+3))
    (i : Fin (k+3)) : ℝ :=
  Paper.parisiGradient β (Paper.parisiSchemeMeasure s) (FRSB.forwardSchemeTime s 1 i,x i)

def scalarFiniteNodeHessian (s : RSBScheme k) (β : ℝ) (x : QuantitativePaper.Field (k+3))
    (i : Fin (k+3)) : ℝ :=
  Paper.parisiHessian β (Paper.parisiSchemeMeasure s) (FRSB.forwardSchemeTime s 1 i,x i)

def scalarFiniteNodeFutureValue (s : RSBScheme k) (β : ℝ) (φ : C(Paper.Overlap,ℝ))
    (x : QuantitativePaper.Field (k+3)) (i : Fin (k+3)) : ℝ :=
  ∫r in Ioi (scalarSchemeTransportNode s i),φ r*scalarFutureSquareExtended β
    (Paper.parisiSchemeMeasure s) (scalarSchemeTransportNode s i) r (x i)
    ∂(Paper.parisiSchemeMeasure s:Measure Paper.Overlap)

def scalarFiniteNodeFutureSlope (s : RSBScheme k) (β : ℝ) (φ : C(Paper.Overlap,ℝ))
    (x : QuantitativePaper.Field (k+3)) (i : Fin (k+3)) : ℝ :=
  ∫r in Ioi (scalarSchemeTransportNode s i),φ r*scalarFutureSquareDerivativeExtended β
    (Paper.parisiSchemeMeasure s) (scalarSchemeTransportNode s i) r (x i)
    ∂(Paper.parisiSchemeMeasure s:Measure Paper.Overlap)

def scalarFiniteSevenTermResponse (s : RSBScheme k) (β : ℝ) (φ : C(Paper.Overlap,ℝ))
    (p : Fin (k+3)) (x : QuantitativePaper.Field (k+3)) (ε center : ℝ) : ℝ :=
  let G:=scalarFiniteNodeGradient s β x
  let H:=scalarFiniteNodeHessian s β x
  let w:=fun i : Fin (k+1)=>s.m (i+1)-s.m i
  let node:=scalarFiniteAtomIndex (k:=k)
  let c:=G p^2-center
  φ (scalarSchemeTransportNode s p)*(H p^2+
      2*(1-Paper.parisiCDF (Paper.parisiSchemeMeasure s) (scalarSchemeTransportNode s p))*G p^2*H p)
    -G p*scalarFiniteNodeFutureSlope s β φ x p
    -2*G p*H p*(∑i,w i*G (node i)*scalarTransportCovarianceLevel s φ (node i) p)
    -c*ε*(∑i,w i*G (node i)*φ (scalarSchemeTransportNode s (node i)))
    +(1/2:ℝ)*c*(∑i,w i*Paper.parisiCDF (Paper.parisiSchemeMeasure s)
      (scalarSchemeTransportNode s (node i))*G (node i)^2*φ (scalarSchemeTransportNode s (node i)))
    +(1/2:ℝ)*c*(∑i,∑j,w i*w j*G (node i)*G (node j)*
      scalarTransportCovarianceLevel s φ (node i) (node j))
    +(1/2:ℝ)*c*(∑i,w i*scalarFiniteNodeFutureValue s β φ x (node i))

def scalarTransportExplicitScore (s : RSBScheme k) (β : ℝ) (φ : C(Paper.Overlap,ℝ))
    (p : Fin (k+3)) (e : Bool) (x : QuantitativePaper.Field (k+3)) (center : ℝ) : ℝ :=
  scalarTransportSquarePartial s β φ p 0 x+
    (scalarTransportGradientSquare s β φ p 0 x-center)*scalarTransportExponentPartial s β φ 0 x+
    ∑i : Fin (k+2),gaussianScoreBilinear (scalarTransportEuclideanExponent s β φ e 0)
      (scalarTransportGradientSquare s β φ p 0) x
      (scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficient s β φ 0) (k+2)
        (EuclideanSpace.single i 1))
      (scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficientDerivative s β φ 0) (k+2)
        (EuclideanSpace.single i 1)) center

theorem scalarTransportSquarePartial_zero (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (p : Fin (k+3)) (x : QuantitativePaper.Field (k+3)) :
    scalarTransportSquarePartial s β φ p 0 x=
      -(β^2)*scalarFiniteNodeGradient s β x p*(φ (scalarSchemeTransportNode s p)*(
        FRSB.parisiSpatialJet β (Paper.parisiSchemeMeasure s) 3 (FRSB.forwardSchemeTime s 1 p) (x p)+
        2*Paper.parisiCDF (Paper.parisiSchemeMeasure s) (scalarSchemeTransportNode s p)*
          scalarFiniteNodeGradient s β x p*scalarFiniteNodeHessian s β x p)+
        scalarFiniteNodeFutureSlope s β φ x p) := by
  unfold scalarTransportSquarePartial scalarTransportNodeGradient
    scalarTransportPotentialVariationSpatial scalarTransportFutureSquareSpatial
  simp only [scalarTransportMeasure_zero,scalarLevelTransport_zero]
  rw [scalarSchemeTransportNode_eq_clock s p (by omega)]
  unfold scalarFiniteNodeGradient scalarFiniteNodeHessian scalarFiniteNodeFutureSlope
  ring

theorem scalarTransportExponentPartial_zero (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (x : QuantitativePaper.Field (k+3)) :
    scalarTransportExponentPartial s β φ 0 x=
      -∑i : Fin (k+1),(s.m (i+1)-s.m i)*(-(β^2/2)*(
        φ (scalarSchemeTransportNode s (scalarFiniteAtomIndex i))*(
          scalarFiniteNodeHessian s β x (scalarFiniteAtomIndex i)+
          Paper.parisiCDF (Paper.parisiSchemeMeasure s) (scalarSchemeTransportNode s (scalarFiniteAtomIndex i))*
            scalarFiniteNodeGradient s β x (scalarFiniteAtomIndex i)^2)+
        scalarFiniteNodeFutureValue s β φ x (scalarFiniteAtomIndex i))) := by
  unfold scalarTransportExponentPartial
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  unfold scalarTransportPotentialVariation scalarTransportFutureSquare
    scalarFiniteNodeHessian scalarFiniteNodeGradient scalarFiniteNodeFutureValue scalarFiniteAtomIndex
  simp only [scalarTransportMeasure_zero,scalarLevelTransport_zero]
  rw [scalarSchemeTransportNode_eq_clock s (i+1) (by omega)]

theorem scalarTransportExplicitScore_seven_terms (s : RSBScheme k) (β : ℝ)
    (hβ : β≠0) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (p : Fin (k+3)) (e : Bool) (x : QuantitativePaper.Field (k+3)) (center : ℝ) :
    scalarTransportExplicitScore s β φ p e x center=
      β^2*scalarFiniteSevenTermResponse s β φ p x (Paper.spinSign e) center+
      2*β^2*φ (scalarSchemeTransportNode s p)*scalarFiniteNodeGradient s β x p*
        scalarFiniteNodeHessian s β x p*(Paper.spinSign e-scalarFiniteNodeGradient s β x p) := by
  unfold scalarTransportExplicitScore
  rw [scalarTransportSquarePartial_zero,scalarTransportExponentPartial_zero,
    scalarTransport_score_covariance_contraction s β hβ φ L hφ h0 h1,
    scalarTransportSquare_zero,scalarTransport_score_expansion s β φ h1]
  have hc : scalarFiniteGradientSquare s β p x=scalarFiniteNodeGradient s β x p^2 := rfl
  rw [hc]
  unfold scalarFiniteSevenTermResponse
  have hdouble : (∑i : Fin (k+1),∑j : Fin (k+1),
      scalarFiniteAtomGradientScore s β x i*scalarFiniteAtomGradientScore s β x j*
        scalarTransportCovarianceLevel s φ (scalarFiniteAtomIndex i) (scalarFiniteAtomIndex j))=
      ∑i : Fin (k+1),∑j : Fin (k+1),(s.m (i+1)-s.m i)*(s.m (j+1)-s.m j)*
        scalarFiniteNodeGradient s β x (scalarFiniteAtomIndex i)*
        scalarFiniteNodeGradient s β x (scalarFiniteAtomIndex j)*
          scalarTransportCovarianceLevel s φ (scalarFiniteAtomIndex i) (scalarFiniteAtomIndex j) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [scalarFiniteAtomGradientScore,scalarFiniteNodeGradient,scalarFiniteAtomIndex]
    ring
  rw [hdouble]
  have hd:=scalar_seven_term_cancellation (β^2) (scalarFiniteNodeGradient s β x p)
    (scalarFiniteNodeHessian s β x p)
    (FRSB.parisiSpatialJet β (Paper.parisiSchemeMeasure s) 3 (FRSB.forwardSchemeTime s 1 p) (x p))
    (Paper.parisiCDF (Paper.parisiSchemeMeasure s) (scalarSchemeTransportNode s p))
    (φ (scalarSchemeTransportNode s p)) (Paper.spinSign e) (scalarFiniteNodeGradient s β x p^2-center)
    (scalarFiniteNodeFutureSlope s β φ x p)
    (fun i : Fin (k+1)=>s.m (i+1)-s.m i)
    (fun i=>scalarFiniteNodeGradient s β x (scalarFiniteAtomIndex i))
    (fun i=>scalarFiniteNodeHessian s β x (scalarFiniteAtomIndex i))
    (fun i=>Paper.parisiCDF (Paper.parisiSchemeMeasure s) (scalarSchemeTransportNode s (scalarFiniteAtomIndex i)))
    (fun i=>φ (scalarSchemeTransportNode s (scalarFiniteAtomIndex i)))
    (fun i=>scalarFiniteNodeFutureValue s β φ x (scalarFiniteAtomIndex i))
    (fun i=>scalarTransportCovarianceLevel s φ (scalarFiniteAtomIndex i) p)
    (fun i j=>scalarTransportCovarianceLevel s φ (scalarFiniteAtomIndex i) (scalarFiniteAtomIndex j))
  convert! hd using 1 <;>
    simp only [scalarFiniteNodeGradient,scalarFiniteNodeHessian,scalarFiniteAtomGradientScore,
      scalarFiniteAtomHessianScore,scalarFiniteAtomIndex] <;> ring

end QuantitativeFollowup
