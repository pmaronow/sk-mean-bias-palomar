module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingObservationGraft
public import FourPapersCommon.FiniteObservationRefinementLeafGeometry

@[expose] public section

/-! A prescribed ancestral vertex survives every observation refinement.
Its true state and common-path geometry are retained by the actual
record projection. Added unary observations create no branch charges. -/
noncomputable section
namespace QuantitativeFollowup
open FourPapersCommon FiniteTerminalGenealogy
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {E S : Type}

@[reducible] def nativeStreamingPadVertexEmbed {j : ℕ} (T : FiniteTerminalGenealogy j) :
    (d:ℕ)→FiniteCascadeRecordVertex T→FiniteCascadeRecordVertex (observationTreePad T d)
  | 0, v => v
  | d+1, v => .child (nativeStreamingPadVertexEmbed T d v)

@[reducible] def nativeStreamingPadStateProject {j : ℕ} (T : FiniteTerminalGenealogy j) :
    (d:ℕ)→E→Records E S (observationTreePad T d)→E×Records E S T
  | 0, H, z => (H,z)
  | d+1, _, z => nativeStreamingPadStateProject T d z.1 z.2

theorem nativeStreamingPadVertexEmbed_depth {j : ℕ} (T : FiniteTerminalGenealogy j)
    (d:ℕ) (v:FiniteCascadeRecordVertex T) :
    (nativeStreamingPadVertexEmbed T d v).depth=v.depth := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih

theorem nativeStreamingPadVertexEmbed_state {j : ℕ} (T : FiniteTerminalGenealogy j)
    (d:ℕ) (v:FiniteCascadeRecordVertex T) (H:E) (z:Records E S (observationTreePad T d)) :
    nativeStreamingVertexState (nativeStreamingPadVertexEmbed T d v) H z=
      nativeStreamingVertexState v (nativeStreamingPadStateProject T d H z).1
        (nativeStreamingPadStateProject T d H z).2 := by
  induction d generalizing H with
  | zero => rfl
  | succ d ih => exact ih z.1 z.2

theorem nativeStreamingPadStateProject_eq_block {j : ℕ} (T : FiniteTerminalGenealogy j)
    (d:ℕ) (z:Records E S (.advance (observationTreePad T d))) :
    nativeStreamingPadStateProject T d z.1 z.2=observationBlockCollapse T d z := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih z.2

theorem nativeStreamingPadVertexEmbed_commonPathDepth {j : ℕ} (T : FiniteTerminalGenealogy j)
    (d:ℕ) (v w:FiniteCascadeRecordVertex T) :
    finiteCascadeCommonPathDepth (observationTreePad T d)
      (nativeStreamingPadVertexEmbed T d v) (nativeStreamingPadVertexEmbed T d w)=
      finiteCascadeCommonPathDepth T v w := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih

@[reducible] def nativeStreamingRefinementVertexEmbed (d:ℕ→ℕ) :
    {j:ℕ}→(T:FiniteTerminalGenealogy j)→FiniteCascadeRecordVertex T→
      FiniteCascadeRecordVertex (observationRefineTree d T)
  | _, .leaf, .root _ => .root .leaf
  | _, .advance T, .root _ => .root _
  | _, @FiniteTerminalGenealogy.advance j T, .child v =>
      .child (nativeStreamingPadVertexEmbed (observationRefineTree d T) (d j)
        (nativeStreamingRefinementVertexEmbed d T v))
  | _, .fork T U, .root _ => .root _
  | _, .fork T U, .left v => .left (nativeStreamingRefinementVertexEmbed d T v)
  | _, .fork T U, .right v => .right (nativeStreamingRefinementVertexEmbed d U v)

theorem nativeStreamingRefinementVertexEmbed_depth (d:ℕ→ℕ) {j:ℕ}
    (T:FiniteTerminalGenealogy j) (v:FiniteCascadeRecordVertex T) :
    (nativeStreamingRefinementVertexEmbed d T v).depth=observationRefinementDepth d v.depth := by
  induction v with
  | root T => cases T <;> rfl
  | child v ih =>
      change (nativeStreamingPadVertexEmbed _ _ _).depth=_
      rw [nativeStreamingPadVertexEmbed_depth]
      exact ih
  | left v ih => exact ih
  | right v ih => exact ih

theorem nativeStreamingRefinementVertexEmbed_state (d:ℕ→ℕ) {j:ℕ}
    (T:FiniteTerminalGenealogy j) (v:FiniteCascadeRecordVertex T)
    (H:E) (z:Records E S (observationRefineTree d T)) :
    nativeStreamingVertexState (nativeStreamingRefinementVertexEmbed d T v) H z=
      nativeStreamingVertexState v H (observationRefinementProject d T z) := by
  induction v generalizing H with
  | root T => cases T <;> rfl
  | @child j T v ih =>
      change nativeStreamingVertexState (nativeStreamingPadVertexEmbed _ (d j) _) z.1 z.2=_
      rw [nativeStreamingPadVertexEmbed_state,nativeStreamingPadStateProject_eq_block]
      exact ih (observationBlockCollapse _ _ z).1 (observationBlockCollapse _ _ z).2
  | left v ih => exact ih H z.1
  | right v ih => exact ih H z.2

theorem nativeStreamingRefinementVertexEmbed_commonPathDepth (d:ℕ→ℕ) {j:ℕ}
    (T:FiniteTerminalGenealogy j) (v w:FiniteCascadeRecordVertex T) :
    finiteCascadeCommonPathDepth (observationRefineTree d T)
      (nativeStreamingRefinementVertexEmbed d T v) (nativeStreamingRefinementVertexEmbed d T w)=
      observationRefinementDepth d (finiteCascadeCommonPathDepth T v w) := by
  induction T with
  | leaf => cases v; cases w; rfl
  | @advance j T ih =>
      cases v with
      | root => cases w <;> rfl
      | child v => cases w with
        | root => rfl
        | child w =>
            change finiteCascadeCommonPathDepth (observationTreePad _ (d j)) _ _=_
            rw [nativeStreamingPadVertexEmbed_commonPathDepth]
            exact ih v w
  | fork T U ihT ihU =>
      cases v with
      | root => cases w <;> rfl
      | left v => cases w with
        | root => rfl
        | left w => exact ihT v w
        | right w => rfl
      | right v => cases w with
        | root => rfl
        | left w => rfl
        | right w => exact ihU v w

end QuantitativeFollowup
