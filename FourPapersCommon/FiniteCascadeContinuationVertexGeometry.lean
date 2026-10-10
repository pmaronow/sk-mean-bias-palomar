module
public import FourPapersCommon.FiniteCascadeContinuationLeafGeometry

@[expose] public section

/-! Every retained vertex remains an actual vertex after a continuation graft;
its field and physical depth are unchanged. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open FiniteTerminalGenealogy
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true

@[reducible] def finiteCascadeContinuationVertexEmbed (U : (j : ℕ)→FiniteTerminalGenealogy j) :
    {j : ℕ} → {T : FiniteTerminalGenealogy j} →
      (v : FiniteCascadeRecordVertex T) → FiniteCascadeRecordVertex T →
        FiniteCascadeRecordVertex (finiteCascadeContinuationGraft U v)
  | _, _, .root _, w => .left w
  | _, _, .child v, .root _ => .root _
  | _, _, .child v, .child w => .child (finiteCascadeContinuationVertexEmbed U v w)
  | _, _, .left v, .root _ => .root _
  | _, _, .left v, .left w => .left (finiteCascadeContinuationVertexEmbed U v w)
  | _, _, .left _, .right w => .right w
  | _, _, .right v, .root _ => .root _
  | _, _, .right _, .left w => .left w
  | _, _, .right v, .right w => .right (finiteCascadeContinuationVertexEmbed U v w)

theorem finiteCascadeContinuationVertexEmbed_depth (U : (j : ℕ)→FiniteTerminalGenealogy j) {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v w : FiniteCascadeRecordVertex T) :
    (finiteCascadeContinuationVertexEmbed U v w).depth = w.depth := by
  induction v with
  | root T => rfl
  | child v ih =>
    cases w with
    | root T => rfl
    | child w => exact ih w
  | left v ih =>
    cases w with
    | root T => rfl
    | left w => exact ih w
    | right w => rfl
  | right v ih =>
    cases w with
    | root T => rfl
    | left w => rfl
    | right w => exact ih w

open SpinGlass.AT
variable {S : Type} [Fintype S]

theorem finiteCascadeContinuationVertexEmbed_field (U : (j : ℕ)→FiniteTerminalGenealogy j) {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v w : FiniteCascadeRecordVertex T) (H : FiniteStateField S)
    (z : Records (FiniteStateField S) S (finiteCascadeContinuationGraft U v)) :
    (finiteCascadeContinuationVertexEmbed U v w).field H z =
      w.field H (finiteCascadeContinuationRecords U v z).1 := by
  induction v generalizing H with
  | root T => rfl
  | child v ih =>
    cases w with
    | root T => rfl
    | child w => exact ih w z.1 z.2
  | left v ih =>
    cases w with
    | root T => rfl
    | left w => exact ih w H z.1
    | right w => rfl
  | right v ih =>
    cases w with
    | root T => rfl
    | left w => rfl
    | right w => exact ih w H z.2

theorem finiteCascadeContinuationVertexEmbed_commonPathDepth
    (U : (j : ℕ)→FiniteTerminalGenealogy j) {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) : ∀w z : FiniteCascadeRecordVertex T,
    finiteCascadeCommonPathDepth (finiteCascadeContinuationGraft U v)
      (finiteCascadeContinuationVertexEmbed U v w) (finiteCascadeContinuationVertexEmbed U v z)=
        finiteCascadeCommonPathDepth T w z := by
  induction v with
  | root T => intros; rfl
  | child v ih =>
      intro w z
      cases w with
      | root T => cases z <;> rfl
      | child w => cases z with
        | root T => rfl
        | child z => exact ih w z
  | left v ih =>
      intro w z
      cases w with
      | root T => cases z <;> rfl
      | left w => cases z with
        | root T => rfl
        | left z => exact ih w z
        | right z => rfl
      | right w => cases z <;> rfl
  | right v ih =>
      intro w z
      cases w with
      | root T => cases z <;> rfl
      | left w => cases z <;> rfl
      | right w => cases z with
        | root T => rfl
        | left z => rfl
        | right z => exact ih w z

theorem finiteCascadeCommonPathDepth_root_left {j : ℕ} (T : FiniteTerminalGenealogy j)
    (w : FiniteCascadeRecordVertex T) :
    finiteCascadeCommonPathDepth T (.root T) w=j := by
  cases T <;> cases w <;> rfl

theorem finiteCascadeContinuationNewLeaf_vertex_commonPathDepth
    (U : (j : ℕ)→FiniteTerminalGenealogy j) {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) : ∀i : ObservationLeaf (U v.depth),
    ∀w : FiniteCascadeRecordVertex T,
    finiteCascadeCommonPathDepth (finiteCascadeContinuationGraft U v)
      (observationLeafVertex (finiteCascadeContinuationGraft U v)
        (finiteCascadeContinuationNewLeaf U v i)) (finiteCascadeContinuationVertexEmbed U v w)=
        finiteCascadeCommonPathDepth T v w := by
  induction v with
  | root T =>
      intro i w
      exact (finiteCascadeCommonPathDepth_root_left T w).symm
  | child v ih =>
      intro i w
      cases w with
      | root T => rfl
      | child w => exact ih i w
  | left v ih =>
      intro i w
      cases w with
      | root T => rfl
      | left w => exact ih i w
      | right w => rfl
  | right v ih =>
      intro i w
      cases w with
      | root T => rfl
      | left w => rfl
      | right w => exact ih i w

theorem finiteCascadeContinuationOldLeaf_vertex
    (U : (j : ℕ)→FiniteTerminalGenealogy j) {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) : ∀i : ObservationLeaf T,
    observationLeafVertex (finiteCascadeContinuationGraft U v)
      (finiteCascadeContinuationOldLeaf U v i)=
        finiteCascadeContinuationVertexEmbed U v (observationLeafVertex T i) := by
  induction v with
  | root T => intros; rfl
  | child v ih => intro i; exact congrArg FiniteCascadeRecordVertex.child (ih i)
  | left v ih =>
      intro i
      cases i with
      | inl i => exact congrArg FiniteCascadeRecordVertex.left (ih i)
      | inr i => rfl
  | right v ih =>
      intro i
      cases i with
      | inl i => rfl
      | inr i => exact congrArg FiniteCascadeRecordVertex.right (ih i)

end FourPapersCommon
