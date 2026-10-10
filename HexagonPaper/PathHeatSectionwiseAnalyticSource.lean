module
public import HexagonPaper.PathHeatSectionwiseSource

@[expose] public section

/-! Genuine analytic source hypotheses on each fixed auxiliary fibre.
Freezing one auxiliary value creates a jointly continuous source in unused
dummy auxiliary coordinates, so the checked conditional Price theorem can
be reused without strengthening any original total-variation hypothesis. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal unitInterval
namespace HexagonPaper
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Z E K X : Type*} [TopologicalSpace Z]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Fintype K] [TopologicalSpace K] [DiscreteTopology K]
  [MeasurableSpace K] [BorelSpace K] [MeasurableSingletonClass K]
variable {a b : ℝ}

structure PathHeatSectionwiseAnalyticSource (a b : ℝ) (hab : a≤b)
    (d : PathHeatSectionwiseSignedSource (Icc a b) E K X) (C : ℝ≥0) : Prop where
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
  ell_growth : ∀z ω p,|d.ell (z,(ω,p))|≤C*(1+‖ω.1‖+‖p‖)



end HexagonPaper
