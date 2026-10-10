module
public import FourPapersCommon.RetainedJetContinuity

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {A E F G : Type*} [TopologicalSpace A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem RetainedJetContinuousOn.precompCLM {f : A→E→F} {Q : Set A} {V : Set E}
    (hf : RetainedJetContinuousOn f Q V) (L : G→L[ℝ]E) (W : Set G)
    (hL : ∀x∈W,L x∈V) : RetainedJetContinuousOn (fun q x=>f q (L x)) Q W := by
  refine ⟨fun q hq x hx=>(hf.smooth q hq (L x) (hL x hx)).comp x L.contDiff.contDiffAt,?_⟩
  intro r
  have hc:=(hf.continuous r).comp (f:=fun w : A×G=>(w.1,L w.2))
    (show ContinuousOn (fun w : A×G=>(w.1,L w.2)) (Q×ˢW) by fun_prop)
    (fun w hw=>⟨hw.1,hL w.2 hw.2⟩)
  have hh:=(ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin r=>L)).continuous.comp_continuousOn hc
  apply hh.congr
  intro w hw
  obtain ⟨u,hu,hxu,hfu⟩:=((hf.smooth w.1 hw.1 (L w.2) (hL w.2 hw.2)).contDiffWithinAt (s:=univ)).contDiffOn'
    (m:=(r:ℕ∞ω)) (by simp) (by simp)
  have hfu' : ContDiffOn ℝ r (f w.1) u:=by simpa using hfu
  have hp : IsOpen (L⁻¹' u):=hu.preimage L.continuous
  have he:=L.iteratedFDerivWithin_comp_right hfu' hu.uniqueDiffOn hp.uniqueDiffOn hxu le_rfl
  rw [iteratedFDerivWithin_of_isOpen r hp hxu,iteratedFDerivWithin_of_isOpen r hu hxu] at he
  exact he

end FourPapersCommon
