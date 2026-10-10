module
public import HexagonPaper.PathHeatSignedJet
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-! Source signed jets pulled back through an arbitrary actual continuous
linear sampling map. The finite coordinate derivatives are proved by the
Fréchet chain rule; no finite Price formula is assumed here. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace HexagonPaper
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [CompactSpace X] [SecondCountableTopology X]
local instance instPullbackPathNormed : NormedAddCommGroup C(X,ℝ) := inferInstance
local instance instPullbackPathSpace : NormedSpace ℝ C(X,ℝ) := inferInstance
local instance instPullbackPathTopo : TopologicalSpace C(X,ℝ) :=
  instPullbackPathNormed.toUniformSpace.toTopologicalSpace
local instance instPullbackPathAdd : AddCommGroup C(X,ℝ) := instPullbackPathNormed.toAddCommGroup
local instance instPullbackPathMod : Module ℝ C(X,ℝ) := instPullbackPathSpace.toModule
local instance instPullbackDualNormed : NormedAddCommGroup (C(X,ℝ)→L[ℝ]ℝ) := inferInstance
local instance instPullbackDualSpace : NormedSpace ℝ (C(X,ℝ)→L[ℝ]ℝ) := inferInstance
local instance instPullbackDualTopo : TopologicalSpace (C(X,ℝ)→L[ℝ]ℝ) :=
  instPullbackDualNormed.toUniformSpace.toTopologicalSpace
local instance instPullbackDualAdd : AddCommGroup (C(X,ℝ)→L[ℝ]ℝ) := instPullbackDualNormed.toAddCommGroup
local instance instPullbackDualMod : Module ℝ (C(X,ℝ)→L[ℝ]ℝ) := instPullbackDualSpace.toModule
variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
local instance instPullbackFiniteDualNormed : NormedAddCommGroup (D→L[ℝ]ℝ) := inferInstance
local instance instPullbackFiniteDualSpace : NormedSpace ℝ (D→L[ℝ]ℝ) := inferInstance
local instance instPullbackFiniteDualTopo : TopologicalSpace (D→L[ℝ]ℝ) :=
  instPullbackFiniteDualNormed.toUniformSpace.toTopologicalSpace
local instance instPullbackFiniteDualAdd : AddCommGroup (D→L[ℝ]ℝ) :=
  instPullbackFiniteDualNormed.toAddCommGroup
local instance instPullbackFiniteDualMod : Module ℝ (D→L[ℝ]ℝ) := instPullbackFiniteDualSpace.toModule

def pathHeatPullbackScore (A : D→L[ℝ]C(X,ℝ)) (S : SignedMeasure X) : D→L[ℝ]ℝ :=
  (pathHeatSignedScore S).comp A

def pathHeatPullbackHessian (A : D→L[ℝ]C(X,ℝ)) (M : SignedMeasure (X×X)) : D→L[ℝ]D→L[ℝ]ℝ :=
  ((ContinuousLinearMap.compL ℝ D C(X,ℝ) ℝ).flip A).comp ((pathHeatSignedHessian M).comp A)

@[simp] theorem pathHeatPullbackScore_apply (A : D→L[ℝ]C(X,ℝ))
    (S : SignedMeasure X) (h : D) :
    pathHeatPullbackScore A S h=∫ᵛx,A h x ∂•S := rfl

@[simp] theorem pathHeatPullbackHessian_apply (A : D→L[ℝ]C(X,ℝ))
    (M : SignedMeasure (X×X)) (h k : D) :
    pathHeatPullbackHessian A M h k=∫ᵛx,A h x.1*A k x.2 ∂•M := rfl

theorem hasFDerivAt_pathHeatPullback (A : D→L[ℝ]C(X,ℝ))
    (f : C(X,ℝ)→ℝ) (S : C(X,ℝ)→SignedMeasure X)
    (hf : ∀p,HasFDerivAt f (pathHeatSignedScore (S p)) p) (x : D) :
    HasFDerivAt (fun u=>f (A u)) (pathHeatPullbackScore A (S (A x))) x := by
  simpa only [Function.comp_def,pathHeatPullbackScore] using (hf (A x)).comp x A.hasFDerivAt

theorem hasFDerivAt_pathHeatPullbackScore (A : D→L[ℝ]C(X,ℝ))
    (S : C(X,ℝ)→SignedMeasure X) (M : C(X,ℝ)→SignedMeasure (X×X))
    (hS : ∀p,HasFDerivAt (fun q=>pathHeatSignedScore (S q)) (pathHeatSignedHessian (M p)) p)
    (x : D) :
    HasFDerivAt (fun u=>pathHeatPullbackScore A (S (A u)))
      (pathHeatPullbackHessian A (M (A x))) x := by
  let P := (ContinuousLinearMap.compL ℝ D C(X,ℝ) ℝ).flip A
  have h := P.hasFDerivAt.comp x ((hS (A x)).comp x A.hasFDerivAt)
  simpa only [Function.comp_def,P,pathHeatPullbackScore,pathHeatPullbackHessian,
    ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply] using h

theorem contDiff_two_pathHeatPullback (A : D→L[ℝ]C(X,ℝ))
    (f : C(X,ℝ)→ℝ) (S : C(X,ℝ)→SignedMeasure X) (M : C(X,ℝ)→SignedMeasure (X×X))
    (hf : ∀p,HasFDerivAt f (pathHeatSignedScore (S p)) p)
    (hS : ∀p,HasFDerivAt (fun q=>pathHeatSignedScore (S q)) (pathHeatSignedHessian (M p)) p)
    (hM : ∀p,Tendsto (fun q=>signedTV (M q-M p)) (𝓝 p) (𝓝 0)) :
    ContDiff ℝ 2 (fun u=>f (A u)) :=
  (contDiff_two_of_pathHeatSignedJets f S M hf hS hM).comp A.contDiff

theorem pathHeatPullback_second_fderiv (A : D→L[ℝ]C(X,ℝ))
    (f : C(X,ℝ)→ℝ) (S : C(X,ℝ)→SignedMeasure X) (M : C(X,ℝ)→SignedMeasure (X×X))
    (hf : ∀p,HasFDerivAt f (pathHeatSignedScore (S p)) p)
    (hS : ∀p,HasFDerivAt (fun q=>pathHeatSignedScore (S q)) (pathHeatSignedHessian (M p)) p)
    (x h k : D) :
    fderiv ℝ (fun u=>fderiv ℝ (fun v=>f (A v)) u) x h k=
      ∫ᵛz,A h z.1*A k z.2 ∂•M (A x) := by
  have he : (fun u=>fderiv ℝ (fun v=>f (A v)) u)=
      fun u=>pathHeatPullbackScore A (S (A u)) := by
    funext u
    exact (hasFDerivAt_pathHeatPullback A f S hf u).fderiv
  rw [he,(hasFDerivAt_pathHeatPullbackScore A S M hS x).fderiv]
  rfl

theorem pathHeatPullback_exp_contDiff (A : D→L[ℝ]C(X,ℝ))
    (f : C(X,ℝ)→ℝ) (S : C(X,ℝ)→SignedMeasure X) (M : C(X,ℝ)→SignedMeasure (X×X))
    (hf : ∀p,HasFDerivAt f (pathHeatSignedScore (S p)) p)
    (hS : ∀p,HasFDerivAt (fun q=>pathHeatSignedScore (S q)) (pathHeatSignedHessian (M p)) p)
    (hM : ∀p,Tendsto (fun q=>signedTV (M q-M p)) (𝓝 p) (𝓝 0)) :
    ContDiff ℝ 2 (fun u=>Real.exp (f (A u))) :=
  (contDiff_two_pathHeatPullback A f S M hf hS hM).exp

theorem second_fderiv_exp_of_jets
    (f : D→ℝ) (S : D→D→L[ℝ]ℝ) (M : D→D→L[ℝ]D→L[ℝ]ℝ)
    (hf : ∀x,HasFDerivAt f (S x) x) (hS : ∀x,HasFDerivAt S (M x) x) (x h k : D) :
    fderiv ℝ (fun u=>fderiv ℝ (fun v=>Real.exp (f v)) u) x h k=
      Real.exp (f x)*(M x h k+S x h*S x k) := by
  have he : (fun u=>fderiv ℝ (fun v=>Real.exp (f v)) u)=
      fun u=>Real.exp (f u)•S u := by
    funext u
    exact (hf u).exp.fderiv
  have hd : HasFDerivAt (fun u=>Real.exp (f u)•S u)
      (Real.exp (f x)•M x+(Real.exp (f x)•S x).smulRight (S x)) x := by
    convert! (hf x).exp.smul (hS x) using 1
  rw [he,hd.fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul]
  ring

theorem second_fderiv_exp_mul_of_jets
    (f g : D→ℝ) (S P : D→D→L[ℝ]ℝ) (M Q : D→D→L[ℝ]D→L[ℝ]ℝ)
    (hf : ∀x,HasFDerivAt f (S x) x) (hg : ∀x,HasFDerivAt g (P x) x)
    (hS : ∀x,HasFDerivAt S (M x) x) (hP : ∀x,HasFDerivAt P (Q x) x) (x h k : D) :
    fderiv ℝ (fun u=>fderiv ℝ (fun v=>Real.exp (f v)*g v) u) x h k=
      Real.exp (f x)*(Q x h k+S x h*P x k+P x h*S x k+
        g x*(M x h k+S x h*S x k)) := by
  have he : (fun u=>fderiv ℝ (fun v=>Real.exp (f v)*g v) u)=
      fun u=>Real.exp (f u)•(g u•S u+P u) := by
    funext u
    have hd : HasFDerivAt (fun v=>Real.exp (f v)*g v)
        (Real.exp (f u)•P u+g u•(Real.exp (f u)•S u)) u := by
      convert! (hf u).exp.mul (hg u) using 1
    rw [hd.fderiv]
    ext v
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
    ring
  have hB : HasFDerivAt (fun u=>g u•S u+P u)
      (g x•M x+(P x).smulRight (S x)+Q x) x := by
    convert! ((hg x).smul (hS x)).add (hP x) using 1
  have hd : HasFDerivAt (fun u=>Real.exp (f u)•(g u•S u+P u))
      (Real.exp (f x)•(g x•M x+(P x).smulRight (S x)+Q x)+
        (Real.exp (f x)•S x).smulRight (g x•S x+P x)) x := by
    convert! (hf x).exp.smul hB using 1
  rw [he,hd.fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul]
  ring

end HexagonPaper
