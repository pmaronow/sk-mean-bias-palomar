module
public import QuantitativeFollowup.ScalarTransportSummationByParts
public import QuantitativeFollowup.ScalarFiniteLocalResponse
public import FourPapersCommon.FiniteTransportSummationFull

@[expose] public section

/-! The boundary in the genuine transported-node response is the actual
Hessian plus the one-sided finite-cell coefficient times the actual squared
gradient. Atom reconciliation with the right-continuous CDF is separate. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT FourPapersCommon OverlapPaper
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 128
variable {k : ℕ}

def scalarTransportBoundaryGradient (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (i : ℕ) (u x : ℝ) : ℝ :=
  Paper.parisiGradient β (scalarTransportMeasure (Paper.parisiSchemeMeasure s) φ u)
    ((scalarLevelTransport φ u (scalarSchemeTransportNode s i):ℝ),x)

def scalarTransportBoundaryHessian (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (i : ℕ) (u x : ℝ) : ℝ :=
  Paper.parisiHessian β (scalarTransportMeasure (Paper.parisiSchemeMeasure s) φ u)
    ((scalarLevelTransport φ u (scalarSchemeTransportNode s i):ℝ),x)

theorem scalarTransportNode_boundary_response (s : RSBScheme k)
    (β : ℝ) (hβ : 0 < β) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ u x : ℝ) (hδ : 0 < δ) (hsmall : δ*L < 1) (hu : |u| ≤ δ)
    (J : ℕ) (hJ : J ≤ k+2) :
    scalarTransportBoundaryHessian s β φ (k+2-J) u x+
      scalarSchemeMass s J*scalarTransportBoundaryGradient s β φ (k+2-J) u x^2=
      1+∑r∈Finset.range J,(scalarSchemeMass s (r+1)-scalarSchemeMass s r)*
        scalarTransportOriginalFuture s β hβ φ L hφ h0 h1 δ u hδ hsmall hu r J x := by
  let r:=scalarTransportRefinedScheme s φ L hφ h0 h1 δ u hδ hsmall hu
  have hr:=scalarGaussianCascade_local_response r β hβ 0 (3*J) (by omega)
    (EuclideanSpace.single (0:Fin 1) x)
  have hm (j : ℕ) : scalarSchemeMass r j=coefficientScheduleMass s j :=
    scalarTransportRefinedScheme_mass s φ L hφ h0 h1 δ u hδ hsmall hu j
  have hmass : scalarSchemeMass r (3*J)=scalarSchemeMass s J := by
    rw [hm]
    simp [coefficientScheduleMass,scalarSchemeMass,Nat.mul_comm]
  have hidx : 3*k+4+2-3*J=3*(k+2-J) := by omega
  have hq : r.q (3*(k+2-J))=
      (scalarLevelTransport φ u (scalarSchemeTransportNode s (k+2-J)):ℝ) :=
    threefoldScheme_q_original _ _ _ _ _
  have hs := sum_threefold_mass_differences_full (scalarSchemeMass s)
    (fun p=>scalarSchemeFutureSquareKernel r β hβ 0 p (3*J)
      (EuclideanSpace.single (0:Fin 1) x)) J
  have hsum : (∑p∈Finset.range (3*J),(scalarSchemeMass r (p+1)-scalarSchemeMass r p)*
      scalarSchemeFutureSquareKernel r β hβ 0 (p+1) (3*J)
        (EuclideanSpace.single (0:Fin 1) x))=
      ∑b∈Finset.range J,(scalarSchemeMass s (b+1)-scalarSchemeMass s b)*
        scalarTransportOriginalFuture s β hβ φ L hφ h0 h1 δ u hδ hsmall hu b J x := by
    simp_rw [hm]
    simpa only [coefficientScheduleMass,scalarSchemeMass,scalarTransportOriginalFuture,r] using hs
  rw [hidx,hq,hmass,hsum] at hr
  rw [scalarTransportRefinedScheme_measure s φ L hφ h0 h1 δ u hδ hsmall hu] at hr
  simpa only [scalarTransportBoundaryHessian,scalarTransportBoundaryGradient,scalarSiteAbsolute,
    PiLp.single_apply,ite_true,zero_add] using hr

theorem scalarTransportNodeScheduleDerivative_finite_stieltjes (s : RSBScheme k)
    (β : ℝ) (hβ : 0 < β) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ u x : ℝ) (hδ : 0 < δ) (hsmall : δ*L < 1) (hu : |u| < δ)
    (J : ℕ) (hJ : J ≤ k+2) :
    scalarTransportNodeScheduleDerivative s β φ δ J u x=
      -(β^2/2)*(
        φ (scalarSchemeTransportNode s (k+2-J))*
          (scalarTransportBoundaryHessian s β φ (k+2-J) u x+
            scalarSchemeMass s J*scalarTransportBoundaryGradient s β φ (k+2-J) u x^2)+
        ∑r∈Finset.range J,(scalarSchemeMass s r-scalarSchemeMass s (r+1))*
          scalarTransportOriginalFuture s β hβ φ L hφ h0 h1 δ u hδ hsmall hu.le r J x*
            φ (scalarSchemeTransportNode s (k+1-r))) := by
  rw [scalarTransportNodeScheduleDerivative_summation_by_parts s β hβ φ L hφ h0 h1 δ u x
    hδ hsmall hu J hJ,
    ←scalarTransportNode_boundary_response s β hβ φ L hφ h0 h1 δ u x hδ hsmall hu.le J hJ]
  have he : (∑r∈Finset.range J,(scalarSchemeMass s r-scalarSchemeMass s (r+1))*
      scalarTransportOriginalFuture s β hβ φ L hφ h0 h1 δ u hδ hsmall hu.le r J x*
        φ (scalarSchemeTransportNode s (k+1-r)))=
      -(∑r∈Finset.range J,(scalarSchemeMass s (r+1)-scalarSchemeMass s r)*
        scalarTransportOriginalFuture s β hβ φ L hφ h0 h1 δ u hδ hsmall hu.le r J x*
          φ (scalarSchemeTransportNode s (k+1-r))) := by
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [he]
  ring

end QuantitativeFollowup
