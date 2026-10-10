module
public import HexagonPaper.PathHeatNativeSourceExtension

@[expose] public section

/-! Literal source regularity with auxiliary coordinates fixed for total
variation continuity. Scalar functions are jointly continuous; the signed
jets need only be continuous in parameter and path in each auxiliary fibre. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction unitInterval
namespace HexagonPaper
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Z E K X : Type*} [TopologicalSpace Z] [TopologicalSpace E] [TopologicalSpace K]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [CompactSpace X] [SecondCountableTopology X]

structure PathHeatSectionwiseSignedSource (Z E K X : Type*)
    [TopologicalSpace Z] [TopologicalSpace E] [TopologicalSpace K]
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [CompactSpace X] [SecondCountableTopology X] where
  ell : Z×((E×K)×C(X,ℝ))→ℝ
  phi : Z×((E×K)×C(X,ℝ))→ℝ
  dotell : Z×((E×K)×C(X,ℝ))→ℝ
  dotphi : Z×((E×K)×C(X,ℝ))→ℝ
  S : Z×((E×K)×C(X,ℝ))→SignedMeasure X
  P : Z×((E×K)×C(X,ℝ))→SignedMeasure X
  M : Z×((E×K)×C(X,ℝ))→SignedMeasure (X×X)
  Q : Z×((E×K)×C(X,ℝ))→SignedMeasure (X×X)
  B : ℝ≥0
  Ds : ℝ≥0
  Dm : ℝ≥0
  Dp : ℝ≥0
  Dq : ℝ≥0
  Dt : ℝ≥0
  Dphi : ℝ≥0
  continuous_ell : Continuous ell
  continuous_phi : Continuous phi
  continuous_dotell : Continuous dotell
  continuous_dotphi : Continuous dotphi
  continuous_S : ∀aux,∀v : Z×C(X,ℝ),Tendsto
    (fun w=>signedTV (S (w.1,(aux,w.2))-S (v.1,(aux,v.2)))) (𝓝 v) (𝓝 0)
  continuous_P : ∀aux,∀v : Z×C(X,ℝ),Tendsto
    (fun w=>signedTV (P (w.1,(aux,w.2))-P (v.1,(aux,v.2)))) (𝓝 v) (𝓝 0)
  continuous_M : ∀aux,∀v : Z×C(X,ℝ),Tendsto
    (fun w=>signedTV (M (w.1,(aux,w.2))-M (v.1,(aux,v.2)))) (𝓝 v) (𝓝 0)
  continuous_Q : ∀aux,∀v : Z×C(X,ℝ),Tendsto
    (fun w=>signedTV (Q (w.1,(aux,w.2))-Q (v.1,(aux,v.2)))) (𝓝 v) (𝓝 0)
  bound_phi : ∀u,|phi u|≤B
  bound_dotell : ∀u,|dotell u|≤Dt
  bound_dotphi : ∀u,|dotphi u|≤Dphi
  bound_S : ∀u,signedTV (S u)≤Ds
  bound_P : ∀u,signedTV (P u)≤Dp
  bound_M : ∀u,signedTV (M u)≤Dm
  bound_Q : ∀u,signedTV (Q u)≤Dq

namespace PathHeatSectionwiseSignedSource
variable (d : PathHeatSectionwiseSignedSource Z E K X)

def «section» (aux : E×K) : PathHeatContinuousSignedSource (Z×C(X,ℝ)) X where
  ell v := d.ell (v.1,(aux,v.2))
  phi v := d.phi (v.1,(aux,v.2))
  dotell v := d.dotell (v.1,(aux,v.2))
  dotphi v := d.dotphi (v.1,(aux,v.2))
  S v := d.S (v.1,(aux,v.2))
  P v := d.P (v.1,(aux,v.2))
  M v := d.M (v.1,(aux,v.2))
  Q v := d.Q (v.1,(aux,v.2))
  B := d.B
  Ds := d.Ds
  Dm := d.Dm
  Dp := d.Dp
  Dq := d.Dq
  Dt := d.Dt
  Dphi := d.Dphi
  continuous_ell := d.continuous_ell.comp
    (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))
  continuous_phi := d.continuous_phi.comp
    (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))
  continuous_dotell := d.continuous_dotell.comp
    (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))
  continuous_dotphi := d.continuous_dotphi.comp
    (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))
  continuous_S := d.continuous_S aux
  continuous_P := d.continuous_P aux
  continuous_M := d.continuous_M aux
  continuous_Q := d.continuous_Q aux
  bound_phi v := d.bound_phi _
  bound_dotell v := d.bound_dotell _
  bound_dotphi v := d.bound_dotphi _
  bound_S v := d.bound_S _
  bound_P v := d.bound_P _
  bound_M v := d.bound_M _
  bound_Q v := d.bound_Q _

def weight (u : Z×((E×K)×C(X,ℝ))) : ℝ := Real.exp (d.ell u)
def densityGenerator (kernel : X×X→ᵇℝ) (u : Z×((E×K)×C(X,ℝ))) : ℝ :=
  pathHeatDensityGenerator kernel (d.S u) (d.M u) (d.dotell u)
def observableGenerator (kernel : X×X→ᵇℝ) (u : Z×((E×K)×C(X,ℝ))) : ℝ :=
  pathHeatObservableGenerator kernel (d.S u) (d.P u) (d.Q u) (d.dotphi u)
def densityBound (κ : ℝ≥0) : ℝ := d.Dt+(1/2:ℝ)*κ*(d.Dm+d.Ds*d.Ds)
def observableBound (κ : ℝ≥0) : ℝ := d.Dphi+(1/2:ℝ)*κ*(d.Dq+2*d.Ds*d.Dp)

theorem continuous_weight : Continuous d.weight := Real.continuous_exp.comp d.continuous_ell
theorem densityBound_nonneg (κ : ℝ≥0) : 0≤d.densityBound κ := by
  unfold densityBound
  positivity
theorem observableBound_nonneg (κ : ℝ≥0) : 0≤d.observableBound κ := by
  unfold observableBound
  positivity

theorem densityGenerator_bound (kernel : X×X→ᵇℝ) (κ : ℝ≥0) (hK : ‖kernel‖≤κ)
    (u : Z×((E×K)×C(X,ℝ))) : |d.densityGenerator kernel u|≤d.densityBound κ :=
  (d.section u.2.1).densityGenerator_bound kernel κ hK (u.1,u.2.2)

theorem observableGenerator_bound (kernel : X×X→ᵇℝ) (κ : ℝ≥0) (hK : ‖kernel‖≤κ)
    (u : Z×((E×K)×C(X,ℝ))) : |d.observableGenerator kernel u|≤d.observableBound κ :=
  (d.section u.2.1).observableGenerator_bound kernel κ hK (u.1,u.2.2)

end PathHeatSectionwiseSignedSource

end HexagonPaper
