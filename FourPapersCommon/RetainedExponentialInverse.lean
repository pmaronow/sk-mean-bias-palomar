module
public import FourPapersCommon.RetainedExponentialContinuous

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {A E B : Type*} [TopologicalSpace A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B] [NormOneClass B] [Nontrivial B]

theorem RetainedExponentialContinuousOn.inverse {f : A→E→B} {Q : Set A} {V : Set E}
    (hf : RetainedExponentialContinuousOn f Q V) (hu : ∀q∈Q,∀x∈V,IsUnit (f q x))
    (D R : ℝ) (hD : 0≤D) (hR : 0≤R)
    (hb : ∀q∈Q,∀x∈V,‖Ring.inverse (f q x)‖≤D*Real.exp (R*‖x‖)) :
    RetainedExponentialContinuousOn (fun q x=>Ring.inverse (f q x)) Q V := by
  refine ⟨?_,D,R,hD,hR,hb⟩
  intro w hw
  have hInv : ContinuousAt Ring.inverse (f w.1 w.2):=by
    simpa only [IsUnit.unit_spec] using
      (analyticAt_inverse (𝕜:=ℝ) (hu w.1 hw.1 w.2 hw.2).unit).continuousAt
  exact hInv.comp_continuousWithinAt (f := fun w : A×E=>f w.1 w.2) (hf.continuous w hw)

end FourPapersCommon
