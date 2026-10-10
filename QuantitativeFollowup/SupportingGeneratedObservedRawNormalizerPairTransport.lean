module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawNormalizerFamily
public import QuantitativeFollowup.SupportingGeneratedObservedRawTaggedBounds
public import QuantitativeFollowup.SupportingGeneratedObservedRawComponentLaw

@[expose] public section

/-! The actual independent normalizer successor carries every old physical
pair and adds the two leaves of its genuine appended binary component.
The source test retains the entire old observable. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n d : ℕ}

private abbrev rawComponentTerminal (n : ℕ) {k : ℕ}
    (U : CavityGeneratedObservedRawComponent k) := TerminalSpins (Configuration (n+1)) U.tree

def observedRawNormalizerComponentLeafCast (U V : CavityGeneratedObservedRawComponent m)
    (he : U = V) (i : ObservationLeaf V.tree) : ObservationLeaf U.tree :=
  cast (congrArg (fun K : CavityGeneratedObservedRawComponent m => ObservationLeaf K.tree) he.symm) i

private theorem componentLeafCast_spin (U V : CavityGeneratedObservedRawComponent m)
    (he : U = V) (i : ObservationLeaf V.tree) (σ : rawComponentTerminal n U) :
    observationTerminalSpin U.tree (observedRawNormalizerComponentLeafCast U V he i) σ =
      observationTerminalSpin V.tree i (cavityGeneratedObservedRawComponentTerminalCastEquiv (n:=n) U V he σ) := by
  cases he
  rfl

private theorem componentLeafCast_commonLevel (U V : CavityGeneratedObservedRawComponent m)
    (he : U = V) (i k : ObservationLeaf V.tree) :
    observationCommonLevel U.tree (observedRawNormalizerComponentLeafCast U V he i) (observedRawNormalizerComponentLeafCast U V he k) =
      observationCommonLevel V.tree i k := by
  cases he
  rfl

def cavityGeneratedObservedRawNormalizerOldLeaf (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (i : ObservationLeaf (W.tree c)) :
    ObservationLeaf ((cavityGeneratedObservedRawNormalizerForest W).tree c.castSucc) :=
  observedRawNormalizerComponentLeafCast _ _ (cavityGeneratedObservedRawNormalizerForest_old_component W c) i

def cavityGeneratedObservedRawNormalizerOldTerminalProjection (W : CavityGeneratedObservedRawForest m)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawNormalizerForest W).depth
      (cavityGeneratedObservedRawNormalizerForest W).tree) :
    CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree :=
  fun c => cavityGeneratedObservedRawComponentTerminalCastEquiv (n:=n) _ _
    (cavityGeneratedObservedRawNormalizerForest_old_component W c) (σ c.castSucc)

def cavityGeneratedObservedRawNormalizerFreshTerminalProjection (W : CavityGeneratedObservedRawForest m)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawNormalizerForest W).depth
      (cavityGeneratedObservedRawNormalizerForest W).tree) :
    TerminalSpins (Configuration (n+1)) anisotropicBinaryObservationTree :=
  cavityGeneratedObservedRawComponentTerminalCastEquiv (n:=n) _ _
    (cavityGeneratedObservedRawNormalizerForest_new_component W) (σ (Fin.last W.componentCount))

def cavityGeneratedObservedRawNormalizerFreshLeaf (W : CavityGeneratedObservedRawForest m) (b : Bool) :
    ObservationLeaf ((cavityGeneratedObservedRawNormalizerForest W).tree (Fin.last W.componentCount)) :=
  observedRawNormalizerComponentLeafCast _ _ (cavityGeneratedObservedRawNormalizerForest_new_component W)
    (if b then Sum.inr () else Sum.inl ())

def cavityGeneratedObservedRawNormalizerOldPair (W : CavityGeneratedObservedRawForest m)
    (t : CavityGeneratedObservedRawPair W) :
    CavityGeneratedObservedRawPair (cavityGeneratedObservedRawNormalizerForest W) where
  component := t.component.castSucc
  first := cavityGeneratedObservedRawNormalizerOldLeaf W t.component t.first
  second := cavityGeneratedObservedRawNormalizerOldLeaf W t.component t.second

def cavityGeneratedObservedRawNormalizerFreshPair (W : CavityGeneratedObservedRawForest m) :
    CavityGeneratedObservedRawPair (cavityGeneratedObservedRawNormalizerForest W) where
  component := Fin.last W.componentCount
  first := cavityGeneratedObservedRawNormalizerFreshLeaf W false
  second := cavityGeneratedObservedRawNormalizerFreshLeaf W true

theorem cavityGeneratedObservedRawNormalizerOldLeaf_terminal_spin
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (i : ObservationLeaf (W.tree c))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawNormalizerForest W).depth
      (cavityGeneratedObservedRawNormalizerForest W).tree) :
    observationTerminalSpin ((cavityGeneratedObservedRawNormalizerForest W).tree c.castSucc)
      (cavityGeneratedObservedRawNormalizerOldLeaf W c i) (σ c.castSucc) =
    observationTerminalSpin (W.tree c) i (cavityGeneratedObservedRawNormalizerOldTerminalProjection W σ c) :=
  componentLeafCast_spin (n:=n) _ _ (cavityGeneratedObservedRawNormalizerForest_old_component W c) i _

theorem cavityGeneratedObservedRawNormalizerFreshLeaf_terminal_spin
    (W : CavityGeneratedObservedRawForest m) (b : Bool)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawNormalizerForest W).depth
      (cavityGeneratedObservedRawNormalizerForest W).tree) :
    observationTerminalSpin ((cavityGeneratedObservedRawNormalizerForest W).tree (Fin.last W.componentCount))
      (cavityGeneratedObservedRawNormalizerFreshLeaf W b) (σ (Fin.last W.componentCount)) =
    if b then (cavityGeneratedObservedRawNormalizerFreshTerminalProjection W σ).2
      else (cavityGeneratedObservedRawNormalizerFreshTerminalProjection W σ).1 := by
  cases b
  all_goals exact (componentLeafCast_spin (n:=n) _ _
    (cavityGeneratedObservedRawNormalizerForest_new_component W) _ _)

theorem cavityGeneratedObservedRawNormalizerForest_old_clock_all
    (W : CavityGeneratedObservedRawForest m)
    (H : CavityGeneratedHistory Paper.Overlap (m+1)) (c : Fin W.componentCount) :
    (cavityGeneratedObservedRawNormalizerForest W).clock H c.castSucc =
      W.clock (H ∘ Fin.castSucc) c := by
  change ((cavityGeneratedObservedRawNormalizerForest W).component c.castSucc).clock H = _
  rw [cavityGeneratedObservedRawNormalizerForest_old_component]
  rfl

theorem cavityGeneratedObservedRawNormalizerForest_fresh_clock
    (W : CavityGeneratedObservedRawForest m)
    (H : CavityGeneratedHistory Paper.Overlap (m+1)) :
    (cavityGeneratedObservedRawNormalizerForest W).clock H (Fin.last W.componentCount) =
      anisotropicBinaryObservationSchedule (H (Fin.last m)) := by
  change ((cavityGeneratedObservedRawNormalizerForest W).component (Fin.last W.componentCount)).clock H = _
  rw [cavityGeneratedObservedRawNormalizerForest_new_component]
  exact cavityGeneratedObservedRawNormalizerComponent_clock H

theorem cavityGeneratedObservedRawNormalizerOldPair_defect
    (W : CavityGeneratedObservedRawForest m) (t : CavityGeneratedObservedRawPair W)
    (H : CavityGeneratedHistory Paper.Overlap (m+1))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawNormalizerForest W).depth
      (cavityGeneratedObservedRawNormalizerForest W).tree) :
    cavityGeneratedObservedRawPairDefect (cavityGeneratedObservedRawNormalizerForest W)
      (cavityGeneratedObservedRawNormalizerOldPair W t) H σ =
      cavityGeneratedObservedRawPairDefect W t (H ∘ Fin.castSucc)
        (cavityGeneratedObservedRawNormalizerOldTerminalProjection W σ) := by
  unfold cavityGeneratedObservedRawPairDefect cavityGeneratedObservedRawNormalizerOldPair
  rw [cavityGeneratedObservedRawNormalizerOldLeaf_terminal_spin,cavityGeneratedObservedRawNormalizerOldLeaf_terminal_spin,
    cavityGeneratedObservedRawNormalizerForest_old_clock_all]
  change cavitySpinOverlapDefect n
    (W.clock (H ∘ Fin.castSucc) t.component
      (observationCommonLevel _
        (observedRawNormalizerComponentLeafCast _ _ (cavityGeneratedObservedRawNormalizerForest_old_component W t.component) t.first)
        (observedRawNormalizerComponentLeafCast _ _ (cavityGeneratedObservedRawNormalizerForest_old_component W t.component) t.second)))
    _ _ = _
  rw [componentLeafCast_commonLevel]
  rfl

theorem cavityGeneratedObservedRawNormalizerFreshPair_defect
    (W : CavityGeneratedObservedRawForest m)
    (H : CavityGeneratedHistory Paper.Overlap (m+1))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawNormalizerForest W).depth
      (cavityGeneratedObservedRawNormalizerForest W).tree) :
    cavityGeneratedObservedRawPairDefect (cavityGeneratedObservedRawNormalizerForest W)
      (cavityGeneratedObservedRawNormalizerFreshPair W) H σ =
      nativeStreamingNormalizerBinaryTerminalTest n (H (Fin.last m))
        (cavityGeneratedObservedRawNormalizerFreshTerminalProjection W σ) := by
  unfold cavityGeneratedObservedRawPairDefect cavityGeneratedObservedRawNormalizerFreshPair
  rw [cavityGeneratedObservedRawNormalizerFreshLeaf_terminal_spin,cavityGeneratedObservedRawNormalizerFreshLeaf_terminal_spin,
    cavityGeneratedObservedRawNormalizerForest_fresh_clock]
  change cavitySpinOverlapDefect n
    (anisotropicBinaryObservationSchedule (H (Fin.last m))
      (observationCommonLevel _
        (observedRawNormalizerComponentLeafCast _ _ (cavityGeneratedObservedRawNormalizerForest_new_component W) (Sum.inl ()))
        (observedRawNormalizerComponentLeafCast _ _ (cavityGeneratedObservedRawNormalizerForest_new_component W) (Sum.inr ()))))
    _ _ = _
  rw [componentLeafCast_commonLevel]
  rfl

def cavityGeneratedObservedRawNormalizerPairSourceTest (W : CavityGeneratedObservedRawForest m)
    (F : CavityGeneratedHistory Paper.Overlap m →
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (H : CavityGeneratedHistory Paper.Overlap (m+1))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawNormalizerForest W).depth
      (cavityGeneratedObservedRawNormalizerForest W).tree) : ℝ :=
  F (H ∘ Fin.castSucc) (cavityGeneratedObservedRawNormalizerOldTerminalProjection W σ) *
    cavityGeneratedObservedRawPairDefect (cavityGeneratedObservedRawNormalizerForest W)
      (cavityGeneratedObservedRawNormalizerFreshPair W) H σ

def cavityGeneratedObservedRawNormalizerTaggedSuccessor (W : CavityGeneratedObservedRawForest m)
    (A : CavityGeneratedObservedRawTaggedTest n W d) :
    CavityGeneratedObservedRawTaggedTest n (cavityGeneratedObservedRawNormalizerForest W) (d+1) where
  base := fun z => A.base (z.1 ∘ Fin.castSucc,cavityGeneratedObservedRawNormalizerOldTerminalProjection W z.2)
  pairs := Fin.snoc (fun i => cavityGeneratedObservedRawNormalizerOldPair W (A.pairs i))
    (cavityGeneratedObservedRawNormalizerFreshPair W)

theorem cavityGeneratedObservedRawNormalizerTaggedSuccessor_value
    (W : CavityGeneratedObservedRawForest m) (A : CavityGeneratedObservedRawTaggedTest n W d)
    (H : CavityGeneratedHistory Paper.Overlap (m+1))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawNormalizerForest W).depth
      (cavityGeneratedObservedRawNormalizerForest W).tree) :
    cavityGeneratedObservedRawTaggedValue (cavityGeneratedObservedRawNormalizerForest W)
      (cavityGeneratedObservedRawNormalizerTaggedSuccessor W A) (H,σ) =
    cavityGeneratedObservedRawNormalizerPairSourceTest W
      (fun h τ => cavityGeneratedObservedRawTaggedValue W A (h,τ)) H σ := by
  unfold cavityGeneratedObservedRawTaggedValue cavityGeneratedObservedRawNormalizerTaggedSuccessor
    cavityGeneratedObservedRawNormalizerPairSourceTest
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last,cavityGeneratedObservedRawNormalizerOldPair_defect]
  ring

theorem measurable_cavityGeneratedObservedRawNormalizerTaggedSuccessor_base
    (W : CavityGeneratedObservedRawForest m) (A : CavityGeneratedObservedRawTaggedTest n W d)
    (hA : Measurable A.base) : Measurable (cavityGeneratedObservedRawNormalizerTaggedSuccessor W A).base := by
  exact hA.comp ((Measurable.of_eval fun i=>
    (measurable_pi_apply i.castSucc).comp measurable_fst).prodMk
    ((measurable_of_finite (cavityGeneratedObservedRawNormalizerOldTerminalProjection (n:=n) W)).comp measurable_snd))

theorem cavityGeneratedObservedRawNormalizerTaggedSuccessor_base_abs_le
    (W : CavityGeneratedObservedRawForest m) (A : CavityGeneratedObservedRawTaggedTest n W d)
    (L : ℝ) (hA : ∀z,|A.base z|≤L) :
    ∀z,|(cavityGeneratedObservedRawNormalizerTaggedSuccessor W A).base z|≤L :=
  fun z=>hA _

end QuantitativeFollowup
