module
public import HexagonPaper.PathHeatJointPartials
public import QuantitativeFollowup.GaussianWeightedParameterResponse

@[expose] public section

/-! Actual finite parameter derivatives are obtained from the source's
separate parameter and signed spatial derivatives. The sampling map is
fixed; no joint second parameter derivative is required. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace HexagonPaper
open QuantitativePaper QuantitativeFollowup
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [CompactSpace X] [SecondCountableTopology X]
variable {n : ℕ}

/-- The source hypotheses are separate path and parameter derivatives,
with continuity of those actual first derivatives. -/
structure PathHeatSignedParameterData
    (f : ℝ→C(X,ℝ)→ℝ) (dot : ℝ×C(X,ℝ)→ℝ)
    (S : ℝ×C(X,ℝ)→SignedMeasure X) (U : Set ℝ) : Prop where
  parameter : ∀z∈U,∀q,HasDerivAt (fun u=>f u q) (dot (z,q)) z
  spatial : ∀z∈U,∀q,HasFDerivAt (f z) (pathHeatSignedScore (S (z,q))) q
  dot_continuous : ∀z∈U,∀p,ContinuousAt dot (z,p)
  score_continuous : ∀z∈U,∀p,
    Tendsto (fun v=>signedTV (S v-S (z,p))) (𝓝 (z,p)) (𝓝 0)

def pathHeatFiniteParameterMap (A : Field n→L[ℝ]C(X,ℝ)) :
    (ℝ×Field n)→L[ℝ](ℝ×C(X,ℝ)) :=
  (ContinuousLinearMap.fst ℝ ℝ (Field n)).prod
    (A.comp (ContinuousLinearMap.snd ℝ ℝ (Field n)))

@[simp] theorem pathHeatFiniteParameterMap_apply
    (A : Field n→L[ℝ]C(X,ℝ)) (v : ℝ×Field n) :
    pathHeatFiniteParameterMap A v=(v.1,A v.2) := rfl

theorem hasFDerivAt_pathHeat_finite_of_signed_partials
    (A : Field n→L[ℝ]C(X,ℝ))
    (f : ℝ→C(X,ℝ)→ℝ) (dot : ℝ×C(X,ℝ)→ℝ)
    (S : ℝ×C(X,ℝ)→SignedMeasure X) (U : Set ℝ) (a : ℝ) (y : Field n)
    (hU : U∈𝓝 a)
    (ht : ∀z∈U,∀q,HasDerivAt (fun u=>f u q) (dot (z,q)) z)
    (hx : ∀z∈U,∀q,HasFDerivAt (f z) (pathHeatSignedScore (S (z,q))) q)
    (hdt : ContinuousAt dot (a,A y))
    (hS : Tendsto (fun v=>signedTV (S v-S (a,A y))) (𝓝 (a,A y)) (𝓝 0)) :
    HasFDerivAt (Function.uncurry (fun z x=>f z (A x)))
      ((ContinuousLinearMap.toSpanSingleton ℝ (dot (a,A y))).coprod
        (pathHeatPullbackScore A (S (a,A y)))) (a,y) := by
  have h := (hasFDerivAt_pathHeat_joint_of_signed_partials
    f dot S U a (A y) hU ht hx hdt hS).comp (a,y)
      (pathHeatFiniteParameterMap A).hasFDerivAt
  convert! h using 1

theorem pathHeat_finite_parameter_derivative
    (A : Field n→L[ℝ]C(X,ℝ))
    (f : ℝ→C(X,ℝ)→ℝ) (dot : ℝ×C(X,ℝ)→ℝ)
    (S : ℝ×C(X,ℝ)→SignedMeasure X) (U : Set ℝ) (a : ℝ) (y : Field n)
    (hU : U∈𝓝 a)
    (ht : ∀z∈U,∀q,HasDerivAt (fun u=>f u q) (dot (z,q)) z)
    (hx : ∀z∈U,∀q,HasFDerivAt (f z) (pathHeatSignedScore (S (z,q))) q)
    (hdt : ContinuousAt dot (a,A y))
    (hS : Tendsto (fun v=>signedTV (S v-S (a,A y))) (𝓝 (a,A y)) (𝓝 0)) :
    gaussianParameterDerivative (fun z x=>f z (A x)) a y=dot (a,A y) := by
  unfold gaussianParameterDerivative
  rw [(hasFDerivAt_pathHeat_finite_of_signed_partials A f dot S U a y hU ht hx hdt hS).fderiv]
  simp [ContinuousLinearMap.toSpanSingleton,pathHeatPullbackScore]

theorem pathHeat_finite_parameter_partials
    (A : Field n→L[ℝ]C(X,ℝ))
    (f : ℝ→C(X,ℝ)→ℝ) (dot : ℝ×C(X,ℝ)→ℝ)
    (S : ℝ×C(X,ℝ)→SignedMeasure X) (U : Set ℝ) (a : ℝ)
    (hU : U∈𝓝 a)
    (ht : ∀z∈U,∀q,HasDerivAt (fun u=>f u q) (dot (z,q)) z)
    (hx : ∀z∈U,∀q,HasFDerivAt (f z) (pathHeatSignedScore (S (z,q))) q)
    (hdt : ∀p,ContinuousAt dot (a,p))
    (hS : ∀p,Tendsto (fun v=>signedTV (S v-S (a,p))) (𝓝 (a,p)) (𝓝 0)) :
    (∀y,DifferentiableAt ℝ (Function.uncurry (fun z x=>f z (A x))) (a,y)) ∧
    (∀y,gaussianParameterDerivative (fun z x=>f z (A x)) a y=dot (a,A y)) ∧
    Measurable (gaussianParameterDerivative (fun z x=>f z (A x)) a) := by
  have he (y : Field n) := pathHeat_finite_parameter_derivative
    A f dot S U a y hU ht hx (hdt (A y)) (hS (A y))
  refine ⟨fun y=>(hasFDerivAt_pathHeat_finite_of_signed_partials
    A f dot S U a y hU ht hx (hdt (A y)) (hS (A y))).differentiableAt,he,?_⟩
  have hslice : Continuous (fun p : C(X,ℝ)=>dot (a,p)) := by
    rw [continuous_iff_continuousAt]
    intro p
    exact (hdt p).comp (continuous_const.prodMk continuous_id).continuousAt
  have hc : Continuous (fun y : Field n=>dot (a,A y)) := hslice.comp A.continuous
  have heq : gaussianParameterDerivative (fun z x=>f z (A x)) a=
      fun y=>dot (a,A y) := funext he
  rw [heq]
  exact hc.measurable

theorem pathHeat_source_finite_parameter_partials
    (A : Field n→L[ℝ]C(X,ℝ))
    (f : ℝ→C(X,ℝ)→ℝ) (dot : ℝ×C(X,ℝ)→ℝ)
    (S : ℝ×C(X,ℝ)→SignedMeasure X) (U : Set ℝ) (a : ℝ)
    (hU : U∈𝓝 a) (h : PathHeatSignedParameterData f dot S U) :
    (∀y,DifferentiableAt ℝ (Function.uncurry (fun z x=>f z (A x))) (a,y)) ∧
    (∀y,gaussianParameterDerivative (fun z x=>f z (A x)) a y=dot (a,A y)) ∧
    Measurable (gaussianParameterDerivative (fun z x=>f z (A x)) a) :=
  pathHeat_finite_parameter_partials A f dot S U a hU h.parameter h.spatial
    (h.dot_continuous a (mem_of_mem_nhds hU))
    (h.score_continuous a (mem_of_mem_nhds hU))

theorem pathHeat_source_finite_exp_parameter_derivatives
    (A : Field n→L[ℝ]C(X,ℝ))
    (ell Phi : ℝ→C(X,ℝ)→ℝ) (dotell dotPhi : ℝ×C(X,ℝ)→ℝ)
    (S P : ℝ×C(X,ℝ)→SignedMeasure X) (U : Set ℝ) (a : ℝ)
    (hU : U∈𝓝 a) (hell : PathHeatSignedParameterData ell dotell S U)
    (hPhi : PathHeatSignedParameterData Phi dotPhi P U) (y : Field n) :
    gaussianParameterDerivative (fun z x=>Real.exp (ell z (A x))) a y=
      Real.exp (ell a (A y))*dotell (a,A y) ∧
    gaussianParameterDerivative (fun z x=>Real.exp (ell z (A x))*Phi z (A x)) a y=
      Real.exp (ell a (A y))*(dotPhi (a,A y)+Phi a (A y)*dotell (a,A y)) := by
  have he := pathHeat_source_finite_parameter_partials A ell dotell S U a hU hell
  have hp := pathHeat_source_finite_parameter_partials A Phi dotPhi P U a hU hPhi
  constructor
  · rw [gaussianParameterDerivative_exp (fun z x=>ell z (A x)) (he.1 y),he.2.1 y]
  · rw [gaussianParameterDerivative_exp_mul (fun z x=>ell z (A x))
      (fun z x=>Phi z (A x)) (he.1 y) (hp.1 y),he.2.1 y,hp.2.1 y]

end HexagonPaper
