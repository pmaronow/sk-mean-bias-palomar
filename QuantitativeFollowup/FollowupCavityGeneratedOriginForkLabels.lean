module
public import QuantitativeFollowup.SupportingGeneratedOriginClockBudget
public import QuantitativeFollowup.FollowupCavityGeneratedForestConstruction

@[expose] public section

/-! Every actual inherited fork charge is routed to a retained generated
history coordinate. The witnesses come from the genuine construction;
neither fixed endpoint labels nor an observation-edge count is substituted
for a generated mark. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
variable {m j : ℕ}

theorem cavityGeneratedOriginForkDepth_pair
    (T : FiniteTerminalGenealogy j) (d : ℕ)
    (hd : d ∈ printedGeneratedOriginForkDepths T) :
    ∃b e : ObservationLeaf T, b ≠ e ∧ observationCommonLevel T b e = d := by
  induction T with
  | leaf =>
      exact (show False by
        simpa only [printedGeneratedOriginForkDepths, List.not_mem_nil] using hd).elim
  | advance T ih => exact ih hd
  | @fork j T U ihT ihU =>
      simp only [printedGeneratedOriginForkDepths, List.mem_append,
        List.mem_singleton] at hd
      rcases hd with (hd | hd) | hd
      · obtain ⟨b,e,hbe,he⟩ := ihT hd
        exact ⟨Sum.inl b,Sum.inl e,fun h => hbe (Sum.inl.inj h),he⟩
      · obtain ⟨b,e,hbe,he⟩ := ihU hd
        exact ⟨Sum.inr b,Sum.inr e,fun h => hbe (Sum.inr.inj h),he⟩
      · subst d
        refine ⟨Sum.inl (cavityGeneratedChosenLeaf T),
          Sum.inr (cavityGeneratedChosenLeaf U),?_,rfl⟩
        intro h
        cases h

theorem cavityGeneratedOriginForkDepth_mark
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (d : ℕ) (hd : d ∈ printedGeneratedOriginForkDepths (W.tree c)) :
    ∃i : Fin m, cavityGeneratedFiniteClockLabels (W.label c) d = .mark i := by
  obtain ⟨b,e,hbe,he⟩ := cavityGeneratedOriginForkDepth_pair (W.tree c) d hd
  simpa only [he] using (W.construction c).pair_clock_labels b e hbe

def cavityGeneratedOriginForkMark
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (d : {d : ℕ // d ∈ printedGeneratedOriginForkDepths (W.tree c)}) : Fin m :=
  Classical.choose (cavityGeneratedOriginForkDepth_mark W c d.val d.property)

def cavityGeneratedOriginForkMarks
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount) : List (Fin m) :=
  (printedGeneratedOriginForkDepths (W.tree c)).attach.map (cavityGeneratedOriginForkMark W c)

theorem cavityGeneratedOriginForkMarks_count
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount) :
    (cavityGeneratedOriginForkMarks W c).length + 1 =
      FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) := by
  simpa only [cavityGeneratedOriginForkMarks,List.length_map,List.length_attach] using
    printedGeneratedOriginForkDepths_count (W.tree c)

theorem cavityGeneratedOriginForkMark_clock
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (d : {d : ℕ // d ∈ printedGeneratedOriginForkDepths (W.tree c)})
    (h : CavityGeneratedHistory Paper.Overlap m) (hh : h ∈ W.clockTemplate.orderSet) :
    W.clockTemplate.clock h c d.val = h (cavityGeneratedOriginForkMark W c d) := by
  obtain ⟨b,e,_,he⟩ := cavityGeneratedOriginForkDepth_pair (W.tree c) d.val d.property
  have hj : d.val ≤ W.depth c := by
    simpa only [he] using cavityGenerated_observationCommonLevel_le (W.tree c) b e
  have hi := Classical.choose_spec (cavityGeneratedOriginForkDepth_mark W c d.val d.property)
  have hl : W.label c ⟨d.val,by omega⟩ = .mark (cavityGeneratedOriginForkMark W c d) := by
    simpa only [cavityGeneratedFiniteClockLabels,dif_pos hj,cavityGeneratedOriginForkMark] using hi
  rw [W.clockTemplate.clock_eq_raw_of_mem h hh c d.val hj]
  change (if hd : d.val ≤ W.depth c then
    (W.label c ⟨d.val,by omega⟩).value h else 0) = _
  rw [dif_pos hj,hl]
  rfl

theorem cavityGeneratedOriginForkSum_eq_history_marks
    (μ : Paper.ParisiMeasure) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (h : CavityGeneratedHistory Paper.Overlap m)
    (hh : h ∈ W.clockTemplate.orderSet) (f : Paper.Overlap → ℝ) :
    ((printedGeneratedOriginForkDepths (W.tree c)).map
      (fun d => Paper.parisiCDF μ (W.clockTemplate.clock h c d)*f (W.clockTemplate.clock h c d))).sum =
    ((cavityGeneratedOriginForkMarks W c).map
      (fun i => Paper.parisiCDF μ (h i)*f (h i))).sum := by
  let L := printedGeneratedOriginForkDepths (W.tree c)
  let A := fun d => Paper.parisiCDF μ (W.clockTemplate.clock h c d)*f (W.clockTemplate.clock h c d)
  let B := fun i => Paper.parisiCDF μ (h i)*f (h i)
  have he : L.map A = (cavityGeneratedOriginForkMarks W c).map B := by
    calc
      L.map A = (L.attach.map Subtype.val).map A :=
        congrArg (List.map A) (List.attach_map_subtype_val L).symm
      _ = L.attach.map (fun d => A d.val) := by rw [List.map_map]; rfl
      _ = L.attach.map (fun d => B (cavityGeneratedOriginForkMark W c d)) := by
        apply List.map_congr_left
        intro d _
        dsimp only [A,B]
        rw [cavityGeneratedOriginForkMark_clock W c d h hh]
      _ = (cavityGeneratedOriginForkMarks W c).map B := by
        simp only [cavityGeneratedOriginForkMarks,List.map_map,Function.comp_def,L]
  exact congrArg List.sum he

theorem cavityGeneratedOriginClockBudget_history_marks
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (h : CavityGeneratedHistory Paper.Overlap m)
    (hh : h ∈ W.clockTemplate.orderSet) (f : Paper.Overlap → ℝ)
    (hf : Integrable f (parisiFreeMeasure μ a)) (hpos : ∀r,0 ≤ f r) :
    nativeStreamingOriginWeightIntegral μ a (W.clockTemplate.clock h c) (W.tree c) a
      (fun o => f (nativeStreamingOriginLevel (W.clockTemplate.clock h c) o)) ≤
    (FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ)*
      (∫r,f r ∂parisiFreeMeasure μ a) +
      ((cavityGeneratedOriginForkMarks W c).map
        (fun i => Paper.parisiCDF μ (h i)*f (h i))).sum := by
  have hq : Antitone (W.clockTemplate.clock h c) :=
    antitone_nat_of_succ_le (fun d => W.clockTemplate.clock_step_le h c d)
  have he := printedGeneratedOriginClockBudget μ a ha hμ (W.clockTemplate.clock h c)
    hq (W.clockTemplate.clock_terminal h c) (W.tree c)
    (W.clockTemplate.clock_initial h c) f hf hpos
  simpa only [cavityGeneratedOriginForkSum_eq_history_marks μ W c h hh f] using he

end QuantitativeFollowup
