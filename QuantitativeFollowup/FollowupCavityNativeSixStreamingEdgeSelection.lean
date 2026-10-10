module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingBlockSelection
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeMarkLaw

@[expose] public section

/-! Select a genuine ancestral state within an arbitrary refined edge
without discarding any original record.  The index is measured from the
lower endpoint of that edge.  Unary padding elsewhere is projected by
the actual observation-refinement map. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {E S : Type} {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

@[reducible] def nativeStreamingBlockSelectionAt {j : ℕ}
    (T : FiniteTerminalGenealogy j) : (d p : ℕ) →
      Records E S (.advance (observationTreePad T d)) → E × (E × Records E S T)
  | 0, _ => fun z => (z.1,z)
  | d+1, p => if p=d then Prod.map id (observationBlockCollapse T d)
      else nativeStreamingBlockSelectionAt T d p ∘ Prod.snd

theorem measurable_nativeStreamingBlockSelectionAt [MeasurableSpace E] [MeasurableSpace S]
    {j : ℕ} (T : FiniteTerminalGenealogy j) (d p : ℕ) :
    Measurable (nativeStreamingBlockSelectionAt (E:=E) (S:=S) T d p) := by
  induction d generalizing p with
  | zero => exact measurable_fst.prodMk measurable_id
  | succ d ih =>
      simp only [nativeStreamingBlockSelectionAt]
      split
      · exact measurable_id.prodMap (measurable_observationBlockCollapse T d)
      · exact (ih p).comp measurable_snd

theorem continuous_nativeStreamingBlockSelectionAt [TopologicalSpace E] [TopologicalSpace S]
    {j : ℕ} (T : FiniteTerminalGenealogy j) (d p : ℕ) :
    Continuous (nativeStreamingBlockSelectionAt (E:=E) (S:=S) T d p) := by
  induction d generalizing p with
  | zero => exact continuous_fst.prodMk continuous_id
  | succ d ih =>
      simp only [nativeStreamingBlockSelectionAt]
      split
      · exact continuous_id.prodMap (continuous_observationBlockCollapse T d)
      · exact (ih p).comp continuous_snd

theorem nativeStreamingBlockSelectionAt_snd {j : ℕ}
    (T : FiniteTerminalGenealogy j) (d p : ℕ)
    (z : Records E S (.advance (observationTreePad T d))) :
    (nativeStreamingBlockSelectionAt T d p z).2=observationBlockCollapse T d z := by
  induction d generalizing p with
  | zero => rfl
  | succ d ih =>
      simp only [nativeStreamingBlockSelectionAt]
      split
      · rfl
      · exact ih p z.2

theorem nativeStreamingBlockSelectionAt_kernel (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (Q : ℕ → Paper.Overlap) (hQ : Antitone Q)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (d p : ℕ) (hp : p<d) :
    (anisotropicRecordedProfileTreeKernel D μ Q (.advance (observationTreePad T d))).map
      (nativeStreamingBlockSelectionAt T d p)=
      (Kernel.id ×ₖ ((Kernel.id ×ₖ anisotropicRecordedProfileTreeKernel D μ Q T) ∘ₖ
        anisotropicObservationTransition D μ (Q (j+p+1)) (Q j))) ∘ₖ
          anisotropicObservationTransition D μ (Q (j+d+1)) (Q (j+p+1)) := by
  induction d generalizing p with
  | zero => omega
  | succ d ih =>
      by_cases he : p=d
      · subst p
        simp only [nativeStreamingBlockSelectionAt,if_pos rfl]
        change ((_ ×ₖ _) ∘ₖ _).map (Prod.map id (observationBlockCollapse T d))=_
        rw [Kernel.map_comp,←Kernel.map_prod_map _ _ measurable_id
          (measurable_observationBlockCollapse T d),Kernel.map_id,
          anisotropicRecordedProfileTreeKernel_block_collapse D μ Q hQ]
        simp only [Nat.add_assoc]
      · have hp' : p<d := by omega
        simp only [nativeStreamingBlockSelectionAt,if_neg he]
        change ((_ ×ₖ _) ∘ₖ _).map (nativeStreamingBlockSelectionAt T d p ∘ Prod.snd)=_
        rw [Kernel.map_comp,Kernel.map_comp_right _ measurable_snd
          (measurable_nativeStreamingBlockSelectionAt T d p),←Kernel.snd_eq,Kernel.snd_prod,
          ih p hp',Kernel.comp_assoc]
        have hc:=anisotropicObservationTransition_semigroup D μ
          (Q (j+(d+1)+1)) (Q (j+d+1)) (Q (j+p+1))
          (hQ (by omega)) (hQ (by omega))
        simp only [Nat.add_assoc] at hc ⊢
        rw [hc]

@[reducible] def nativeStreamingEdgeSelection (d : ℕ → ℕ) :
    {j : ℕ} → {T : FiniteTerminalGenealogy j} → NativeStreamingEdge T → (p : ℕ) →
      Records E S (observationRefineTree d T) → E × Records E S T
  | _, _, @NativeStreamingEdge.here j T, p => fun z =>
      let selected := nativeStreamingBlockSelectionAt (observationRefineTree d T) (d j) p z
      (selected.1,(selected.2.1,observationRefinementProject d T selected.2.2))
  | _, _, @NativeStreamingEdge.child j T e, p => fun z =>
      let block := observationBlockCollapse (observationRefineTree d T) (d j) z
      let selected := nativeStreamingEdgeSelection d e p block.2
      (selected.1,(block.1,selected.2))
  | _, _, @NativeStreamingEdge.left j T U e, p => fun z =>
      let selected := nativeStreamingEdgeSelection d e p z.1
      (selected.1,(selected.2,observationRefinementProject d U z.2))
  | _, _, @NativeStreamingEdge.right j T U e, p => fun z =>
      let selected := nativeStreamingEdgeSelection d e p z.2
      (selected.1,(observationRefinementProject d T z.1,selected.2))

theorem measurable_nativeStreamingEdgeSelection [MeasurableSpace E] [MeasurableSpace S]
    (d : ℕ → ℕ) {j : ℕ} {T : FiniteTerminalGenealogy j} (e : NativeStreamingEdge T) (p : ℕ) :
    Measurable (nativeStreamingEdgeSelection (E:=E) (S:=S) d e p) := by
  induction e with
  | @here j T =>
      have hs:=measurable_nativeStreamingBlockSelectionAt (E:=E) (S:=S)
        (observationRefineTree d T) (d j) p
      exact hs.fst.prodMk (hs.snd.fst.prodMk
        ((measurable_observationRefinementProject d T).comp hs.snd.snd))
  | @child j T e ih =>
      have hc:=measurable_observationBlockCollapse (E:=E) (S:=S)
        (observationRefineTree d T) (d j)
      have hs:=ih.comp hc.snd
      exact hs.fst.prodMk (hc.fst.prodMk hs.snd)
  | @left j T U e ih =>
      have hs : Measurable (fun z : Records E S (observationRefineTree d T) ×
          Records E S (observationRefineTree d U) => nativeStreamingEdgeSelection d e p z.1) :=
        ih.comp measurable_fst
      exact hs.fst.prodMk (hs.snd.prodMk
        ((measurable_observationRefinementProject d _).comp measurable_snd))
  | @right j T U e ih =>
      have hs : Measurable (fun z : Records E S (observationRefineTree d T) ×
          Records E S (observationRefineTree d U) => nativeStreamingEdgeSelection d e p z.2) :=
        ih.comp measurable_snd
      exact hs.fst.prodMk (((measurable_observationRefinementProject d _).comp
        measurable_fst).prodMk hs.snd)

theorem continuous_nativeStreamingEdgeSelection [TopologicalSpace E] [TopologicalSpace S]
    (d : ℕ → ℕ) {j : ℕ} {T : FiniteTerminalGenealogy j} (e : NativeStreamingEdge T) (p : ℕ) :
    Continuous (nativeStreamingEdgeSelection (E:=E) (S:=S) d e p) := by
  induction e with
  | @here j T =>
      have hs:=continuous_nativeStreamingBlockSelectionAt (E:=E) (S:=S)
        (observationRefineTree d T) (d j) p
      exact hs.fst.prodMk (hs.snd.fst.prodMk
        ((continuous_observationRefinementProject d T).comp hs.snd.snd))
  | @child j T e ih =>
      have hc:=continuous_observationBlockCollapse (E:=E) (S:=S)
        (observationRefineTree d T) (d j)
      have hs:=ih.comp hc.snd
      exact hs.fst.prodMk (hc.fst.prodMk hs.snd)
  | @left j T U e ih =>
      have hs : Continuous (fun z : Records E S (observationRefineTree d T) ×
          Records E S (observationRefineTree d U) => nativeStreamingEdgeSelection d e p z.1) :=
        ih.comp continuous_fst
      exact hs.fst.prodMk (hs.snd.prodMk
        ((continuous_observationRefinementProject d _).comp continuous_snd))
  | @right j T U e ih =>
      have hs : Continuous (fun z : Records E S (observationRefineTree d T) ×
          Records E S (observationRefineTree d U) => nativeStreamingEdgeSelection d e p z.2) :=
        ih.comp continuous_snd
      exact hs.fst.prodMk (((continuous_observationRefinementProject d _).comp
        continuous_fst).prodMk hs.snd)

theorem nativeStreamingEdgeSelection_snd (d : ℕ → ℕ)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (e : NativeStreamingEdge T) (p : ℕ)
    (z : Records E S (observationRefineTree d T)) :
    (nativeStreamingEdgeSelection d e p z).2=observationRefinementProject d T z := by
  induction e with
  | here T =>
      change Prod.map id (observationRefinementProject d T)
        (nativeStreamingBlockSelectionAt (observationRefineTree d T) _ p z).2=_
      rw [nativeStreamingBlockSelectionAt_snd]
      rfl
  | child e ih =>
      change (_, (nativeStreamingEdgeSelection d e p _).2)=_
      rw [ih]
      rfl
  | left e ih =>
      change ((nativeStreamingEdgeSelection d e p _).2,_)=_
      rw [ih]
      rfl
  | right e ih =>
      change (_,(nativeStreamingEdgeSelection d e p _).2)=_
      rw [ih]
      rfl

end QuantitativeFollowup
