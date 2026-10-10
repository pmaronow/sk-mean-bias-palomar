module
public import QuantitativeFollowup.ScalarTransportBoundary
public import QuantitativeFollowup.ScalarPartialCovarianceRestart
public import QuantitativeFollowup.ScalarFutureContinuity

@[expose] public section

/-! Every original-node future moment in the actual transported recursion
is the genuine fresh restarted diffusion moment. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT FourPapersCommon OverlapPaper
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

def scalarTransportFutureSquare (β : ℝ) (μ : Paper.ParisiMeasure)
    (φ : C(Paper.Overlap,ℝ)) (u : ℝ) (q r : Paper.Overlap) (x : ℝ) : ℝ :=
  scalarFutureSquareExtended β (scalarTransportMeasure μ φ u)
    (scalarLevelTransport φ u q) (scalarLevelTransport φ u r) x

theorem scalarTransportOriginalFuture_eq_restart (s : RSBScheme k)
    (β : ℝ) (hβ : 0 < β) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ u x : ℝ) (hδ : 0 < δ) (hsmall : δ*L < 1) (hu : |u| ≤ δ)
    (r J : ℕ) (hr : r < J) (hJ : J ≤ k+2) :
    scalarTransportOriginalFuture s β hβ φ L hφ h0 h1 δ u hδ hsmall hu r J x=
      scalarTransportFutureSquare β (Paper.parisiSchemeMeasure s) φ u
        (scalarSchemeTransportNode s (k+2-J)) (scalarSchemeTransportNode s (k+1-r)) x := by
  let a:=scalarTransportRefinedScheme s φ L hφ h0 h1 δ u hδ hsmall hu
  have hstart : scalarFiniteOverlapNode a (3*k+4+2-3*J) (by omega)=
      scalarLevelTransport φ u (scalarSchemeTransportNode s (k+2-J)) := by
    apply Subtype.ext
    dsimp only [scalarFiniteOverlapNode]
    rw [show 3*k+4+2-3*J=3*(k+2-J) by omega]
    exact threefoldScheme_q_original _ _ _ _ _
  have hend : scalarFiniteOverlapNode a (3*k+4+2-3*(r+1)) (by omega)=
      scalarLevelTransport φ u (scalarSchemeTransportNode s (k+1-r)) := by
    apply Subtype.ext
    dsimp only [scalarFiniteOverlapNode]
    rw [show 3*k+4+2-3*(r+1)=3*(k+1-r) by omega]
    exact threefoldScheme_q_original _ _ _ _ _
  have horder : (scalarLevelTransport φ u (scalarSchemeTransportNode s (k+2-J)):ℝ) ≤
      scalarLevelTransport φ u (scalarSchemeTransportNode s (k+1-r)) := by
    have hs:=(strictMono_scalarLevelTransport φ L hφ h0 h1 u
      (scalarTransport_parameter_small L δ u hsmall hu)).monotone
    apply hs
    change (scalarSchemeTransportNode s (k+2-J):ℝ) ≤ scalarSchemeTransportNode s (k+1-r)
    rw [scalarSchemeTransportNode_coe s _ (by omega),scalarSchemeTransportNode_coe s _ (by omega)]
    exact s.q_mono' (k+1-r) (by omega) (k+2-J) (by omega)
  unfold scalarTransportOriginalFuture
  rw [scalarSchemeFutureSquareKernel_eq_restart a β hβ 0 (3*(r+1)) (3*J) (by omega)
    (by omega) (EuclideanSpace.single (0:Fin 1) x)]
  rw [←scalarFutureSquareExtended_eq]
  rw [hstart,hend,scalarTransportRefinedScheme_measure s φ L hφ h0 h1 δ u hδ hsmall hu]
  simp only [scalarTransportFutureSquare,PiLp.single_apply,ite_true,zero_add]

theorem scalarTransportFutureSquare_self (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (φ : C(Paper.Overlap,ℝ)) (u : ℝ) (q : Paper.Overlap) (x : ℝ) :
    scalarTransportFutureSquare β μ φ u q q x=
      Paper.parisiGradient β (scalarTransportMeasure μ φ u) ((scalarLevelTransport φ u q:ℝ),x)^2 := by
  unfold scalarTransportFutureSquare
  rw [scalarFutureSquareExtended_eq β _ _ _ le_rfl x,
    scalarFutureSquare_self β hβ]

end QuantitativeFollowup
