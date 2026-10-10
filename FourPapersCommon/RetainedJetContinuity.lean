module
public import FourPapersCommon.PartialFDerivSmooth
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-! Continuous retained jets of a family with a merely continuous outside
parameter. This asserts no derivative in that outside parameter. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
variable {A E F G : Type*} [TopologicalSpace A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

structure RetainedJetContinuousOn (f : A→E→F) (Q : Set A) (V : Set E) : Prop where
  smooth : ∀q∈Q,∀x∈V,ContDiffAt ℝ ∞ (f q) x
  continuous : ∀r : ℕ,ContinuousOn (fun w : A×E=>iteratedFDeriv ℝ r (f w.1) w.2) (Q×ˢV)

theorem RetainedJetContinuousOn.values {f : A→E→F} {Q : Set A} {V : Set E}
    (hf : RetainedJetContinuousOn f Q V) : ContinuousOn (fun w : A×E=>f w.1 w.2) (Q×ˢV) := by
  have h:=hf.continuous 0
  let L:=(continuousMultilinearCurryFin0 ℝ E F)
  have hh:=L.continuous.comp_continuousOn h
  apply hh.congr
  intro w hw
  change f w.1 w.2=(continuousMultilinearCurryFin0 ℝ E F) (iteratedFDeriv ℝ 0 (f w.1) w.2)
  rw [iteratedFDeriv_zero_eq_comp]
  simp only [Function.comp_apply,LinearIsometryEquiv.apply_symm_apply]

theorem RetainedJetContinuousOn.congr {f g : A→E→F} {Q : Set A} {V : Set E}
    (hf : RetainedJetContinuousOn f Q V)
    (he : ∀q∈Q,∀x∈V,f q=ᶠ[𝓝 x]g q) : RetainedJetContinuousOn g Q V := by
  refine ⟨fun q hq x hx=>(hf.smooth q hq x hx).congr_of_eventuallyEq (he q hq x hx).symm,?_⟩
  intro r
  apply (hf.continuous r).congr
  intro w hw
  exact ((he w.1 hw.1 w.2 hw.2).iteratedFDeriv ℝ r).eq_of_nhds.symm

theorem RetainedJetContinuousOn.compCLM {f : A→E→F} {Q : Set A} {V : Set E}
    (hf : RetainedJetContinuousOn f Q V) (L : F→L[ℝ]G) :
    RetainedJetContinuousOn (fun q x=>L (f q x)) Q V := by
  refine ⟨fun q hq x hx=>L.contDiff.contDiffAt.comp x (hf.smooth q hq x hx),?_⟩
  intro r
  have h:=(ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin r=>E) F G L).continuous.comp_continuousOn
    (hf.continuous r)
  apply h.congr
  intro w hw
  exact L.iteratedFDeriv_comp_left (hf.smooth w.1 hw.1 w.2 hw.2) (by simp)

theorem RetainedJetContinuousOn.fderiv {f : A→E→F} {Q : Set A} {V : Set E}
    (hf : RetainedJetContinuousOn f Q V) :
    RetainedJetContinuousOn (fun q=>fderiv ℝ (f q)) Q V := by
  refine ⟨fun q hq x hx=>(hf.smooth q hq x hx).fderiv_right (m:=∞) (by simp),?_⟩
  intro r
  have h:=(continuousMultilinearCurryRightEquiv' ℝ r E F).continuous.comp_continuousOn
    (hf.continuous (r+1))
  apply h.congr
  intro w hw
  change iteratedFDeriv ℝ r (_root_.fderiv ℝ (f w.1)) w.2=
    (continuousMultilinearCurryRightEquiv' ℝ r E F) (iteratedFDeriv ℝ (r+1) (f w.1) w.2)
  rw [iteratedFDeriv_succ_eq_comp_right]
  simp only [Function.comp_apply,LinearIsometryEquiv.apply_symm_apply]

theorem RetainedJetContinuousOn.directional {f : A→E→F} {Q : Set A} {V : Set E}
    (hf : RetainedJetContinuousOn f Q V) (v : E) :
    RetainedJetContinuousOn (fun q x=>_root_.fderiv ℝ (f q) x v) Q V :=
  hf.fderiv.compCLM (ContinuousLinearMap.apply ℝ F v)

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem RetainedJetContinuousOn.partialFDeriv {f : A→P×E→F} {Q : Set A} {V : Set (P×E)}
    (hf : RetainedJetContinuousOn f Q V) (hV : IsOpen V) :
    RetainedJetContinuousOn (fun q z=>_root_.fderiv ℝ (fun x=>f q (z.1,x)) z.2) Q V := by
  let L : ((P×E)→L[ℝ]F)→L[ℝ](E→L[ℝ]F):=
    (ContinuousLinearMap.compL ℝ E (P×E) F).flip (ContinuousLinearMap.inr ℝ P E)
  apply (hf.fderiv.compCLM L).congr
  intro q hq z hz
  filter_upwards [hV.mem_nhds hz] with w hw
  exact (partial_fderiv_eq (f q) w.1 w.2 ((hf.smooth q hq w hw).differentiableAt (by simp))).symm

theorem RetainedJetContinuousOn.partialGradient {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {f : A→P×E→ℝ} {Q : Set A} {V : Set (P×E)}
    (hf : RetainedJetContinuousOn f Q V) (hV : IsOpen V) :
    RetainedJetContinuousOn (fun q z=>gradient (fun x=>f q (z.1,x)) z.2) Q V :=
  (hf.partialFDeriv hV).compCLM
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem RetainedJetContinuousOn.partialHessian {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {f : A→P×E→ℝ} {Q : Set A} {V : Set (P×E)}
    (hf : RetainedJetContinuousOn f Q V) (hV : IsOpen V) :
    RetainedJetContinuousOn (fun q z=>QuantitativeFollowup.hessianOperator
      (fun x=>f q (z.1,x)) z.2) Q V := by
  apply ((hf.partialGradient hV).partialFDeriv hV).congr
  intro q hq z hz
  filter_upwards [hV.mem_nhds hz] with w hw
  have hC : ContDiffAt ℝ 2 (fun x=>f q (w.1,x)) w.2:=
    ((hf.smooth q hq w hw).comp w.2 (contDiffAt_const.prodMk contDiffAt_id)).of_le (by norm_num)
  exact (hasFDerivAt_gradient_of_contDiffAt _ w.2 hC).fderiv

end FourPapersCommon
