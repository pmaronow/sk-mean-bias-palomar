module
public import FourPapersCommon.FiniteCascadeVertexGraft

@[expose] public section

/-! Every retained vertex remains an actual vertex after a terminal graft;
its field and physical depth are unchanged. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open FiniteTerminalGenealogy
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true

@[reducible] def finiteCascadeGraftVertexEmbed :
    {j : ℕ} → {T : FiniteTerminalGenealogy j} →
      (v : FiniteCascadeRecordVertex T) → FiniteCascadeRecordVertex T →
        FiniteCascadeRecordVertex (finiteCascadeVertexGraft v)
  | _, _, .root _, w => .left w
  | _, _, .child v, .root _ => .root _
  | _, _, .child v, .child w => .child (finiteCascadeGraftVertexEmbed v w)
  | _, _, .left v, .root _ => .root _
  | _, _, .left v, .left w => .left (finiteCascadeGraftVertexEmbed v w)
  | _, _, .left _, .right w => .right w
  | _, _, .right v, .root _ => .root _
  | _, _, .right _, .left w => .left w
  | _, _, .right v, .right w => .right (finiteCascadeGraftVertexEmbed v w)

theorem finiteCascadeGraftVertexEmbed_depth {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v w : FiniteCascadeRecordVertex T) :
    (finiteCascadeGraftVertexEmbed v w).depth = w.depth := by
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

theorem finiteCascadeGraftVertexEmbed_field {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v w : FiniteCascadeRecordVertex T) (H : FiniteStateField S)
    (z : Records (FiniteStateField S) S (finiteCascadeVertexGraft v)) :
    (finiteCascadeGraftVertexEmbed v w).field H z =
      w.field H (finiteCascadeGraftRecordExtract v z).1 := by
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

end FourPapersCommon
