module
public import QuantitativeFollowup.FixedRowSymmetryPosteriorTransportOuter

@[expose] public section

/-! The retained-field affine map depends continuously on every genuine
Gaussian input map. This uses finite-dimensional operator topology and the
actual chronological recursion. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
namespace QuantitativeFollowup
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 160000

theorem continuous_cavityIndependentHistory_parameter
    {B E Z : Type} [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace Z]
    (u : B → ℕ → E → Z → E)
    (hu : ∀ j, Continuous (fun p : B × (E × Z) => u p.1 j p.2.1 p.2.2))
    (N : ℕ) (H : E) (z : Fin N → Z) :
    Continuous (fun b => independentHistory (u b) N (H,z)) := by
  induction N with
  | zero => exact continuous_const
  | succ N ih =>
      apply continuous_pi
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [independentHistory, Fin.snoc_last]
        exact (hu N).comp (continuous_id.prodMk
          (((continuous_apply (Fin.last N)).comp (ih (fun j => z j.castSucc))).prodMk
            continuous_const))
      · simp only [independentHistory, Fin.snoc_castSucc]
        exact (continuous_apply j).comp (ih (fun j => z j.castSucc))

variable {S : Type} [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}

theorem continuous_cavityPosteriorLineFieldLinear
    {B : Type} [TopologicalSpace B]
    (L : B → ℕ → QuantitativePaper.Field n →L[ℝ] FiniteStateField S)
    (hL : ∀ j, Continuous (fun b => L b j)) (N d : ℕ) :
    Continuous (fun b => cavityPosteriorLineFieldLinear (L b) N d) := by
  apply continuous_clm_apply.mpr
  intro z
  simp_rw [cavityPosteriorLineFieldLinear_apply]
  have hu : ∀ j, Continuous (fun p : B × (FiniteStateField S × QuantitativePaper.Field n) =>
      cascadePosteriorUpdate (L p.1) N j p.2.1 p.2.2) := by
    intro j
    unfold cascadePosteriorUpdate
    exact continuous_snd.fst.add (((hL (N-1-j)).comp continuous_fst).clm_apply
      continuous_snd.snd)
  exact (continuous_apply (⟨N-d,by omega⟩ : Fin (N+1))).comp
    (continuous_cavityIndependentHistory_parameter
      (fun b => cascadePosteriorUpdate (L b) N) hu N 0 z)

end QuantitativeFollowup
