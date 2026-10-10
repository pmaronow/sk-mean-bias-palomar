module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawProperties

@[expose] public section

/-! A pair's genuine branch is one of the actual observed forks.
Its clock is therefore a retained coordinate on the computed raw source
support, with no assumption about the number or labels of unary cuts. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {m J : ℕ}

theorem cavityGeneratedObservedRawPair_forkDepth
    (T : FiniteTerminalGenealogy J) (b e : ObservationLeaf T) (hbe : b≠e) :
    observationCommonLevel T b e∈printedGeneratedOriginForkDepths T := by
  induction T with
  | leaf => exact (hbe (Subsingleton.elim _ _)).elim
  | advance T ih => exact ih b e hbe
  | fork T U ihT ihU =>
      simp only [printedGeneratedOriginForkDepths,List.mem_append,List.mem_singleton]
      cases b with
      | inl b => cases e with
        | inl e =>
            exact Or.inl (Or.inl (ihT b e (fun he=>hbe (congrArg Sum.inl he))))
        | inr e => exact Or.inr rfl
      | inr b => cases e with
        | inl e => exact Or.inr rfl
        | inr e =>
            exact Or.inl (Or.inr (ihU b e (fun he=>hbe (congrArg Sum.inr he))))

theorem cavityGeneratedObservedRawComponent_pair_clock_is_mark
    (U : CavityGeneratedObservedRawComponent m) (b e : ObservationLeaf U.tree)
    (hbe : b≠e) (h : CavityGeneratedHistory Paper.Overlap m) (hh : h∈U.supportSet) :
    ∃i : Fin m, U.clock h (observationCommonLevel U.tree b e)=h i := by
  have hd := cavityGeneratedObservedRawPair_forkDepth U.tree b e hbe
  rw [←cavityGeneratedOriginForkVertices_depths] at hd
  obtain ⟨v,hv,he⟩ := List.mem_map.mp hd
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hv
  refine ⟨U.forkMark i,?_⟩
  have hp := U.fork_clock_is_mark h hh i
  rw [hi,he] at hp
  exact hp

theorem cavityGeneratedObservedRawForest_pair_clock_is_mark
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (b e : ObservationLeaf (W.tree c)) (hbe : b≠e)
    (h : CavityGeneratedHistory Paper.Overlap m) (hh : h∈W.supportSet) :
    ∃i : Fin m, W.clock h c (observationCommonLevel (W.tree c) b e)=h i :=
  cavityGeneratedObservedRawComponent_pair_clock_is_mark (W.component c) b e hbe h (hh c)

end QuantitativeFollowup
