module
public import HexagonPaper.PathHeatSectionwiseAnalyticSource
public import HexagonPaper.PathHeatFiniteTreeGrowth

@[expose] public section

/-! The manuscript's native finite-coordinate/tree analytic hypotheses.
The growth bound uses the actual Euclidean finite vector and the actual
edge path supremum norms. All derivative assumptions are genuine Taylor
or fixed-coordinate parameter derivatives; no response formula is assumed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal unitInterval BigOperators
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Fintype K] [TopologicalSpace K] [DiscreteTopology K]
  [MeasurableSpace K] [BorelSpace K] [MeasurableSingletonClass K]
variable {A J : ℕ} {a b : ℝ}

structure PathHeatFiniteTreeSourceHypotheses (a b : ℝ) (hab : a≤b)
    (d : PathHeatSectionwiseSignedSource (Icc a b) E K (pathHeatFiniteTreeIndex A J))
    (C : ℝ≥0) : Prop where
  ell_derivative : ∀z ω p,HasFDerivAt (fun q=>d.ell (z,(ω,q)))
    (pathHeatSignedScore (d.S (z,(ω,p)))) p
  phi_derivative : ∀z ω p,HasFDerivAt (fun q=>d.phi (z,(ω,q)))
    (pathHeatSignedScore (d.P (z,(ω,p)))) p
  score_derivative : ∀z ω p,HasFDerivAt (fun q=>pathHeatSignedScore (d.S (z,(ω,q))))
    (pathHeatSignedHessian (d.M (z,(ω,p)))) p
  phi_score_derivative : ∀z ω p,HasFDerivAt (fun q=>pathHeatSignedScore (d.P (z,(ω,q))))
    (pathHeatSignedHessian (d.Q (z,(ω,p)))) p
  ell_parameter : ∀ω z,z∈Ioo a b→∀p,
    HasDerivAt (fun u=>d.ell (projIcc a b hab u,(ω,p)))
      (d.dotell (projIcc a b hab z,(ω,p))) z
  phi_parameter : ∀ω z,z∈Ioo a b→∀p,
    HasDerivAt (fun u=>d.phi (projIcc a b hab u,(ω,p)))
      (d.dotphi (projIcc a b hab z,(ω,p))) z
  ell_growth : ∀z ω p,|d.ell (z,(ω,p))|≤C*(1+‖ω.1‖+
    ‖pathHeatNativeFiniteVector p‖+∑j : Fin J,‖pathHeatNativeTreePath p j‖)

theorem PathHeatFiniteTreeSourceHypotheses.analytic
    (hab : a≤b)
    (d : PathHeatSectionwiseSignedSource (Icc a b) E K (pathHeatFiniteTreeIndex A J))
    (C : ℝ≥0) (h : PathHeatFiniteTreeSourceHypotheses a b hab d C) :
    PathHeatSectionwiseAnalyticSource a b hab d (C*(1+A+J)) :=
  ⟨h.ell_derivative,h.phi_derivative,h.score_derivative,h.phi_score_derivative,
    h.ell_parameter,h.phi_parameter,
    pathHeatFiniteTree_separate_growth_to_joint d.ell C h.ell_growth⟩

end HexagonPaper
