module
public import QuantitativePaper.VectorFieldSliceJetBounds

@[expose] public section

/-! Genuine joint continuity of every spatial partial jet of a smooth
parameterized function. The slice is a translation followed by a fixed linear
insertion, whose actual multilinear derivatives are identified. -/
noncomputable section
open scoped ContDiff
namespace QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {A E F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem iteratedFDeriv_fieldSlice_eq (f : A×E → F) (hf : ContDiff ℝ ∞ f)
    (j : ℕ) (a : A) (x : E) :
    iteratedFDeriv ℝ j (fun y => f (a,y)) x=
      (iteratedFDeriv ℝ j f (a,x)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ A E) := by
  let L : E →L[ℝ] A×E := ContinuousLinearMap.inr ℝ A E
  let G : A×E → F := fun z => f (z+(a,0))
  have hG : ContDiff ℝ ∞ G := hf.comp (contDiff_id.add contDiff_const)
  have he : (fun y => f (a,y))=G ∘ L := by funext y;simp [G,L,Function.comp_def]
  rw [he,L.iteratedFDeriv_comp_right hG x (by simp),iteratedFDeriv_comp_add_right]
  simp only [L,ContinuousLinearMap.inr_apply,zero_add,add_zero,Prod.mk_add_mk]

theorem continuous_fieldSlice_iteratedFDeriv (f : A×E → F) (hf : ContDiff ℝ ∞ f)
    (j : ℕ) :
    Continuous (fun z : A×E => iteratedFDeriv ℝ j (fun y => f (z.1,y)) z.2) := by
  have he := funext (fun z : A×E => iteratedFDeriv_fieldSlice_eq f hf j z.1 z.2)
  rw [he]
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin j => ContinuousLinearMap.inr ℝ A E)).continuous.comp
      (hf.continuous_iteratedFDeriv (by simp))

end QuantitativePaper
