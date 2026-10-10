module
public import FourPapersCommon.RetainedExponentialContinuous

@[expose] public section

noncomputable section
open Set
namespace FourPapersCommon
variable {A E F : Type*} [TopologicalSpace A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem RetainedExponentialContinuousOn.norm {f : A→E→F} {Q : Set A} {V : Set E}
    (hf : RetainedExponentialContinuousOn f Q V) :
    RetainedExponentialContinuousOn (fun q x=>‖f q x‖) Q V := by
  refine ⟨hf.continuous.norm,?_⟩
  obtain ⟨C,R,hC,hR,hb⟩:=hf.bound
  exact ⟨C,R,hC,hR,fun q hq x hx=>by simpa only [norm_norm] using hb q hq x hx⟩

end FourPapersCommon
