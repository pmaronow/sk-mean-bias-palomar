module
public import HexagonPaper.PathHeatSignedJetPullback
public import Mathlib.Analysis.Calculus.FDeriv.Partial

@[expose] public section

/-! Joint first differentiability follows from the source's continuous
parameter partial and TV-continuous signed spatial partial. No mixed
parameter/path second derivative is required. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [CompactSpace X] [SecondCountableTopology X]

theorem hasFDerivAt_pathHeat_joint_of_signed_partials
    (f : ℝ→C(X,ℝ)→ℝ) (dot : ℝ×C(X,ℝ)→ℝ)
    (S : ℝ×C(X,ℝ)→SignedMeasure X) (U : Set ℝ) (a : ℝ) (p : C(X,ℝ))
    (hU : U∈𝓝 a)
    (ht : ∀z∈U,∀q,HasDerivAt (fun u=>f u q) (dot (z,q)) z)
    (hx : ∀z∈U,∀q,HasFDerivAt (f z) (pathHeatSignedScore (S (z,q))) q)
    (hdt : ContinuousAt dot (a,p))
    (hS : Tendsto (fun v=>signedTV (S v-S (a,p))) (𝓝 (a,p)) (𝓝 0)) :
    HasFDerivAt (Function.uncurry f)
      ((ContinuousLinearMap.toSpanSingleton ℝ (dot (a,p))).coprod
        (pathHeatSignedScore (S (a,p)))) (a,p) := by
  have hu : ∀ᶠv : ℝ×C(X,ℝ) in 𝓝 (a,p),v.1∈U :=
    (continuous_fst.continuousAt.tendsto).eventually hU
  have hd : ContinuousAt (fun v : ℝ×C(X,ℝ)=>ContinuousLinearMap.toSpanSingleton ℝ (dot v)) (a,p) := by
    convert ((ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ→L[ℝ]ℝ)).continuous.continuousAt.comp hdt) using 1
    funext v
    ext t
    simp [ContinuousLinearMap.toSpanSingleton,ContinuousLinearMap.smulRightL]
  have hs : ContinuousAt (fun v : ℝ×C(X,ℝ)=>pathHeatSignedScore (S v)) (a,p) :=
    tendsto_pathHeatSignedScore S (S (a,p)) hS
  have h := hasStrictFDerivAt_uncurry_coprod
    (f:=f)
    (f₁:=fun z q=>ContinuousLinearMap.toSpanSingleton ℝ (dot (z,q)))
    (f₂:=fun z q=>pathHeatSignedScore (S (z,q)))
    (hu.mono fun v hv=>(ht v.1 hv v.2).hasFDerivAt)
    (hu.mono fun v hv=>hx v.1 hv v.2) hd hs
  exact h.hasFDerivAt

end HexagonPaper
