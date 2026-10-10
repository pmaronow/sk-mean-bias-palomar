module
public import QuantitativeFollowup.ScalarTransportRestartFuture
public import QuantitativeFollowup.ScalarSchemeStieltjesBoundary

@[expose] public section

/-! The literal moved-node potential variation in the paper, under the
actual transported overlap law and actual restarted diffusion. The
right-continuous CDF includes every atom at the starting node, and the
future Stieltjes integral is strict there. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT FourPapersCommon OverlapPaper
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

def scalarTransportPotentialVariation (β : ℝ) (μ : Paper.ParisiMeasure)
    (φ : C(Paper.Overlap,ℝ)) (u : ℝ) (q : Paper.Overlap) (x : ℝ) : ℝ :=
  -(β^2/2)*(
    φ q*(Paper.parisiHessian β (scalarTransportMeasure μ φ u) ((scalarLevelTransport φ u q:ℝ),x)+
      Paper.parisiCDF μ q*Paper.parisiGradient β (scalarTransportMeasure μ φ u)
        ((scalarLevelTransport φ u q:ℝ),x)^2)+
    ∫r in Ioi q,φ r*scalarTransportFutureSquare β μ φ u q r x ∂(μ:Measure Paper.Overlap))

theorem scalarTransportNodeScheduleDerivative_eq_variation (s : RSBScheme k)
    (β : ℝ) (hβ : 0 < β) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ u x : ℝ) (hδ : 0 < δ) (hsmall : δ*L < 1) (hu : |u| < δ)
    (J : ℕ) (hJ : J ≤ k+2) :
    scalarTransportNodeScheduleDerivative s β φ δ J u x=
      scalarTransportPotentialVariation β (Paper.parisiSchemeMeasure s) φ u
        (scalarSchemeTransportNode s (k+2-J)) x := by
  let q:=scalarSchemeTransportNode s (k+2-J)
  let F:=fun r:Paper.Overlap=>φ r*scalarTransportFutureSquare β (Paper.parisiSchemeMeasure s) φ u q r x
  have hb:=scalarScheme_stieltjes_boundary s J hJ F
  have hself : F q=φ q*scalarTransportBoundaryGradient s β φ (k+2-J) u x^2 := by
    dsimp only [F,q,scalarTransportBoundaryGradient]
    rw [scalarTransportFutureSquare_self β hβ.ne']
  have hsum : (∑r∈Finset.range J,(scalarSchemeMass s r-scalarSchemeMass s (r+1))*
      scalarTransportOriginalFuture s β hβ φ L hφ h0 h1 δ u hδ hsmall hu.le r J x*
        φ (scalarSchemeTransportNode s (k+1-r)))=
      ∑r∈Finset.range J,(scalarSchemeMass s r-scalarSchemeMass s (r+1))*
        F (scalarSchemeTransportNode s (k+1-r)) := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [scalarTransportOriginalFuture_eq_restart s β hβ φ L hφ h0 h1 δ u x hδ hsmall hu.le
      r J (Finset.mem_range.mp hr) hJ]
    dsimp only [F,q]
    ring
  have hint : (∫r,if q < r then F r else 0 ∂(Paper.parisiSchemeMeasure s:Measure Paper.Overlap))=
      ∫r in Ioi q,F r ∂(Paper.parisiSchemeMeasure s:Measure Paper.Overlap) := by
    rw [←integral_indicator isOpen_Ioi.measurableSet]
    rfl
  change scalarSchemeMass s J*F q+(∑r∈Finset.range J,
    (scalarSchemeMass s r-scalarSchemeMass s (r+1))*F (scalarSchemeTransportNode s (k+1-r)))=
      Paper.parisiCDF (Paper.parisiSchemeMeasure s) q*F q+
        ∫r,if q < r then F r else 0 ∂(Paper.parisiSchemeMeasure s:Measure Paper.Overlap) at hb
  rw [hself,hint] at hb
  rw [scalarTransportNodeScheduleDerivative_finite_stieltjes s β hβ φ L hφ h0 h1 δ u x
    hδ hsmall hu J hJ,hsum]
  dsimp only [scalarTransportPotentialVariation]
  change -(β^2/2)*(φ q*(scalarTransportBoundaryHessian s β φ (k+2-J) u x+
      scalarSchemeMass s J*scalarTransportBoundaryGradient s β φ (k+2-J) u x^2)+_)=
    -(β^2/2)*(φ q*(scalarTransportBoundaryHessian s β φ (k+2-J) u x+
      Paper.parisiCDF (Paper.parisiSchemeMeasure s) q*scalarTransportBoundaryGradient s β φ (k+2-J) u x^2)+_)
  congr 1
  nlinarith [hb]

theorem hasDerivAt_scalarTransportNodePotential_variation (s : RSBScheme k)
    (β : ℝ) (hβ : 0 < β) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ u x : ℝ) (hδ : 0 < δ) (hsmall : δ*L < 1) (hu : |u| < δ)
    (J : ℕ) (hJ : J ≤ k+2) :
    HasDerivAt (fun v=>scalarTransportNodePotential s β φ (k+2-J) v x)
      (scalarTransportPotentialVariation β (Paper.parisiSchemeMeasure s) φ u
        (scalarSchemeTransportNode s (k+2-J)) x) u := by
  rw [←scalarTransportNodeScheduleDerivative_eq_variation s β hβ φ L hφ h0 h1 δ u x
    hδ hsmall hu J hJ]
  exact hasDerivAt_scalarTransportNodePotential_schedule s β hβ φ L hφ h0 h1 δ u x
    hδ hsmall hu J hJ

end QuantitativeFollowup
