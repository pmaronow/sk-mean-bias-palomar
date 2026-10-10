module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingVertexRefinement
public import QuantitativeFollowup.AnisotropicRecordedObservationRefinement

@[expose] public section

/-! Collapse a unary observation block while retaining a selected genuine
interior ancestral state and the complete original lower record.  The
selected state is distributed by the two actual restart transitions,
with every discarded observation removed by the proved semigroup law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {E S : Type} {n : ℕ}
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

@[reducible] def nativeStreamingBlockSelection {j : ℕ}
    (T : FiniteTerminalGenealogy j) (b : ℕ) : (d : ℕ) →
    Records E S (.advance (observationTreePad T (b+1+d))) →
      E × (E × Records E S T)
  | 0 => Prod.map id (observationBlockCollapse T b)
  | d+1 => nativeStreamingBlockSelection T b d ∘ Prod.snd

theorem measurable_nativeStreamingBlockSelection [MeasurableSpace E] [MeasurableSpace S]
    {j : ℕ} (T : FiniteTerminalGenealogy j) (b d : ℕ) :
    Measurable (nativeStreamingBlockSelection (E:=E) (S:=S) T b d) := by
  induction d with
  | zero => exact measurable_id.prodMap (measurable_observationBlockCollapse T b)
  | succ d ih => exact ih.comp measurable_snd

theorem continuous_nativeStreamingBlockSelection [TopologicalSpace E] [TopologicalSpace S]
    {j : ℕ} (T : FiniteTerminalGenealogy j) (b d : ℕ) :
    Continuous (nativeStreamingBlockSelection (E:=E) (S:=S) T b d) := by
  induction d with
  | zero => exact continuous_id.prodMap (continuous_observationBlockCollapse T b)
  | succ d ih => exact ih.comp continuous_snd

@[reducible] def nativeStreamingBlockSelectedVertex {j : ℕ}
    (T : FiniteTerminalGenealogy j) (b : ℕ) : (d : ℕ) →
    FiniteCascadeRecordVertex (.advance (observationTreePad T (b+1+d)))
  | 0 => .child (.root (.advance (observationTreePad T b)))
  | d+1 => .child (nativeStreamingBlockSelectedVertex T b d)

theorem nativeStreamingBlockSelectedVertex_depth {j : ℕ}
    (T : FiniteTerminalGenealogy j) (b d : ℕ) :
    (nativeStreamingBlockSelectedVertex T b d).depth=j+b+1 := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih

theorem nativeStreamingBlockSelectedVertex_state {j : ℕ}
    (T : FiniteTerminalGenealogy j) (b d : ℕ) (H : E)
    (z : Records E S (.advance (observationTreePad T (b+1+d)))) :
    nativeStreamingVertexState (nativeStreamingBlockSelectedVertex T b d) H z=
      (nativeStreamingBlockSelection T b d z).1 := by
  induction d generalizing H with
  | zero => rfl
  | succ d ih => exact ih z.1 z.2

theorem nativeStreamingBlockSelection_snd {j : ℕ}
    (T : FiniteTerminalGenealogy j) (b d : ℕ)
    (z : Records E S (.advance (observationTreePad T (b+1+d)))) :
    (nativeStreamingBlockSelection T b d z).2=
      observationBlockCollapse T (b+1+d) z := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih z.2

theorem nativeStreamingBlockSelection_kernel (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (Q : ℕ → Paper.Overlap) (hQ : Antitone Q)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (b d : ℕ) :
    (anisotropicRecordedProfileTreeKernel D μ Q
      (.advance (observationTreePad T (b+1+d)))).map
        (nativeStreamingBlockSelection T b d)=
      (Kernel.id ×ₖ ((Kernel.id ×ₖ anisotropicRecordedProfileTreeKernel D μ Q T) ∘ₖ
        anisotropicObservationTransition D μ (Q (j+b+1)) (Q j))) ∘ₖ
          anisotropicObservationTransition D μ (Q (j+(b+1+d)+1)) (Q (j+b+1)) := by
  induction d with
  | zero =>
      change ((Kernel.id ×ₖ anisotropicRecordedProfileTreeKernel D μ Q
        (.advance (observationTreePad T b))) ∘ₖ _).map
          (Prod.map id (observationBlockCollapse T b))=_
      rw [Kernel.map_comp,←Kernel.map_prod_map _ _ measurable_id
        (measurable_observationBlockCollapse T b),Kernel.map_id,
        anisotropicRecordedProfileTreeKernel_block_collapse D μ Q hQ]
      simp only [Nat.add_zero,Nat.add_assoc]
  | succ d ih =>
      change ((Kernel.id ×ₖ anisotropicRecordedProfileTreeKernel D μ Q
        (.advance (observationTreePad T (b+1+d)))) ∘ₖ
          anisotropicObservationTransition D μ (Q (j+(b+1+d)+1+1))
            (Q (j+(b+1+d)+1))).map
              (nativeStreamingBlockSelection T b d ∘ Prod.snd)=_
      rw [Kernel.map_comp,Kernel.map_comp_right _ measurable_snd
        (measurable_nativeStreamingBlockSelection T b d),←Kernel.snd_eq,Kernel.snd_prod,
        ih,Kernel.comp_assoc,
        anisotropicObservationTransition_semigroup D μ
          (Q (j+(b+1+d)+1+1)) (Q (j+(b+1+d)+1)) (Q (j+b+1))
          (hQ (by omega)) (hQ (by omega))]
      congr 3 <;> omega

end QuantitativeFollowup
