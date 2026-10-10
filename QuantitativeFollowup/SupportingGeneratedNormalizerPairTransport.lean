module
public import QuantitativeFollowup.FollowupCavityGeneratedStreamingTaggedTests
public import QuantitativeFollowup.SupportingGeneratedNormalizerSourceReceiver

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

def normalizerComponentLeafCast (U V : CavityGeneratedConstructedComponent m)
    (he : U = V) (i : ObservationLeaf V.tree) : ObservationLeaf U.tree :=
  cast (congrArg (fun K : CavityGeneratedConstructedComponent m => ObservationLeaf K.tree) he.symm) i

private theorem componentLeafCast_spin (U V : CavityGeneratedConstructedComponent m)
    (he : U = V) (i : ObservationLeaf V.tree) (σ : CavityGeneratedComponentTerminal n U) :
    observationTerminalSpin U.tree (normalizerComponentLeafCast U V he i) σ =
      observationTerminalSpin V.tree i (cavityGeneratedComponentTerminalCastEquiv (n:=n) U V he σ) := by
  cases he
  rfl

private theorem componentLeafCast_commonLevel (U V : CavityGeneratedConstructedComponent m)
    (he : U = V) (i k : ObservationLeaf V.tree) :
    observationCommonLevel U.tree (normalizerComponentLeafCast U V he i) (normalizerComponentLeafCast U V he k) =
      observationCommonLevel V.tree i k := by
  cases he
  rfl

private theorem componentTerminalCast_record (U V : CavityGeneratedConstructedComponent m)
    (he : U = V) (z : PrintedGeneratedComponentRecord n U) :
    finiteCascadeRecordTerminalSpins V.tree
        (cast (congrArg (PrintedGeneratedComponentRecord n) he) z).2 =
      cavityGeneratedComponentTerminalCastEquiv (n:=n) U V he
        (finiteCascadeRecordTerminalSpins U.tree z.2) := by
  cases he
  rfl

def printedGeneratedNormalizerOldLeaf (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (i : ObservationLeaf (W.tree c)) :
    ObservationLeaf ((printedGeneratedNormalizerAppendedForest W).tree c.castSucc) :=
  normalizerComponentLeafCast _ _ (printedGeneratedNormalizerAppendedForest_old_component W c) i

def printedGeneratedNormalizerOldTerminalProjection (W : CavityGeneratedConstructedForest m)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (printedGeneratedNormalizerAppendedForest W).depth
      (printedGeneratedNormalizerAppendedForest W).tree) :
    CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree :=
  fun c => cavityGeneratedComponentTerminalCastEquiv (n:=n) _ _
    (printedGeneratedNormalizerAppendedForest_old_component W c) (σ c.castSucc)

def printedGeneratedNormalizerFreshTerminalProjection (W : CavityGeneratedConstructedForest m)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (printedGeneratedNormalizerAppendedForest W).depth
      (printedGeneratedNormalizerAppendedForest W).tree) :
    TerminalSpins (Configuration (n+1)) anisotropicBinaryObservationTree :=
  cavityGeneratedComponentTerminalCastEquiv (n:=n) _ _
    (printedGeneratedNormalizerAppendedForest_new_component W) (σ (Fin.last W.componentCount))

def printedGeneratedNormalizerFreshLeaf (W : CavityGeneratedConstructedForest m) (b : Bool) :
    ObservationLeaf ((printedGeneratedNormalizerAppendedForest W).tree (Fin.last W.componentCount)) :=
  normalizerComponentLeafCast _ _ (printedGeneratedNormalizerAppendedForest_new_component W)
    (if b then Sum.inr () else Sum.inl ())

def printedGeneratedNormalizerOldPair (W : CavityGeneratedConstructedForest m)
    (t : CavityGeneratedForestPair W) :
    CavityGeneratedForestPair (printedGeneratedNormalizerAppendedForest W) where
  component := t.component.castSucc
  first := printedGeneratedNormalizerOldLeaf W t.component t.first
  second := printedGeneratedNormalizerOldLeaf W t.component t.second

def printedGeneratedNormalizerFreshPair (W : CavityGeneratedConstructedForest m) :
    CavityGeneratedForestPair (printedGeneratedNormalizerAppendedForest W) where
  component := Fin.last W.componentCount
  first := printedGeneratedNormalizerFreshLeaf W false
  second := printedGeneratedNormalizerFreshLeaf W true

theorem printedGeneratedNormalizerOldLeaf_terminal_spin
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (i : ObservationLeaf (W.tree c))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (printedGeneratedNormalizerAppendedForest W).depth
      (printedGeneratedNormalizerAppendedForest W).tree) :
    observationTerminalSpin ((printedGeneratedNormalizerAppendedForest W).tree c.castSucc)
      (printedGeneratedNormalizerOldLeaf W c i) (σ c.castSucc) =
    observationTerminalSpin (W.tree c) i (printedGeneratedNormalizerOldTerminalProjection W σ c) :=
  componentLeafCast_spin (n:=n) _ _ (printedGeneratedNormalizerAppendedForest_old_component W c) i _

theorem printedGeneratedNormalizerFreshLeaf_terminal_spin
    (W : CavityGeneratedConstructedForest m) (b : Bool)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (printedGeneratedNormalizerAppendedForest W).depth
      (printedGeneratedNormalizerAppendedForest W).tree) :
    observationTerminalSpin ((printedGeneratedNormalizerAppendedForest W).tree (Fin.last W.componentCount))
      (printedGeneratedNormalizerFreshLeaf W b) (σ (Fin.last W.componentCount)) =
    if b then (printedGeneratedNormalizerFreshTerminalProjection W σ).2
      else (printedGeneratedNormalizerFreshTerminalProjection W σ).1 := by
  cases b
  all_goals exact (componentLeafCast_spin (n:=n) _ _
    (printedGeneratedNormalizerAppendedForest_new_component W) _ _)

theorem printedGeneratedNormalizerAppendedForest_old_clock_all
    (W : CavityGeneratedConstructedForest m)
    (H : CavityGeneratedHistory Paper.Overlap (m+1)) (c : Fin W.componentCount) :
    (printedGeneratedNormalizerAppendedForest W).clockTemplate.clock H c.castSucc =
      W.clockTemplate.clock (H ∘ Fin.castSucc) c := by
  rw [←printedGeneratedComponentClock_of_forest,
    printedGeneratedNormalizerAppendedForest_old_component,
    printedGeneratedComponentClock_of_forest]
  exact W.reindex_clock Fin.castSucc (H ∘ Fin.castSucc) H (fun _ => rfl) c

theorem printedGeneratedNormalizerAppendedForest_fresh_clock
    (W : CavityGeneratedConstructedForest m)
    (H : CavityGeneratedHistory Paper.Overlap (m+1)) :
    (printedGeneratedNormalizerAppendedForest W).clockTemplate.clock H (Fin.last W.componentCount) =
      anisotropicBinaryObservationSchedule (H (Fin.last m)) := by
  rw [←printedGeneratedComponentClock_of_forest,
    printedGeneratedNormalizerAppendedForest_new_component,printedGeneratedSiblingClock_binary]

theorem printedGeneratedNormalizerOldPair_defect
    (W : CavityGeneratedConstructedForest m) (t : CavityGeneratedForestPair W)
    (H : CavityGeneratedHistory Paper.Overlap (m+1))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (printedGeneratedNormalizerAppendedForest W).depth
      (printedGeneratedNormalizerAppendedForest W).tree) :
    cavityGeneratedForestPairDefect n (printedGeneratedNormalizerAppendedForest W)
      (printedGeneratedNormalizerOldPair W t) H σ =
      cavityGeneratedForestPairDefect n W t (H ∘ Fin.castSucc)
        (printedGeneratedNormalizerOldTerminalProjection W σ) := by
  unfold cavityGeneratedForestPairDefect printedGeneratedNormalizerOldPair
  rw [printedGeneratedNormalizerOldLeaf_terminal_spin,printedGeneratedNormalizerOldLeaf_terminal_spin,
    printedGeneratedNormalizerAppendedForest_old_clock_all]
  change cavitySpinOverlapDefect n
    (W.clockTemplate.clock (H ∘ Fin.castSucc) t.component
      (observationCommonLevel _
        (normalizerComponentLeafCast _ _ (printedGeneratedNormalizerAppendedForest_old_component W t.component) t.first)
        (normalizerComponentLeafCast _ _ (printedGeneratedNormalizerAppendedForest_old_component W t.component) t.second)))
    _ _ = _
  rw [componentLeafCast_commonLevel]
  rfl

theorem printedGeneratedNormalizerFreshPair_defect
    (W : CavityGeneratedConstructedForest m)
    (H : CavityGeneratedHistory Paper.Overlap (m+1))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (printedGeneratedNormalizerAppendedForest W).depth
      (printedGeneratedNormalizerAppendedForest W).tree) :
    cavityGeneratedForestPairDefect n (printedGeneratedNormalizerAppendedForest W)
      (printedGeneratedNormalizerFreshPair W) H σ =
      nativeStreamingNormalizerBinaryTerminalTest n (H (Fin.last m))
        (printedGeneratedNormalizerFreshTerminalProjection W σ) := by
  unfold cavityGeneratedForestPairDefect printedGeneratedNormalizerFreshPair
  rw [printedGeneratedNormalizerFreshLeaf_terminal_spin,printedGeneratedNormalizerFreshLeaf_terminal_spin,
    printedGeneratedNormalizerAppendedForest_fresh_clock]
  change cavitySpinOverlapDefect n
    (anisotropicBinaryObservationSchedule (H (Fin.last m))
      (observationCommonLevel _
        (normalizerComponentLeafCast _ _ (printedGeneratedNormalizerAppendedForest_new_component W) (Sum.inl ()))
        (normalizerComponentLeafCast _ _ (printedGeneratedNormalizerAppendedForest_new_component W) (Sum.inr ()))))
    _ _ = _
  rw [componentLeafCast_commonLevel]
  rfl

theorem printedGeneratedNormalizerOldTerminalProjection_record
    (W : CavityGeneratedConstructedForest m)
    (z : CavityGeneratedForestRecord (n:=n)
      (printedGeneratedNormalizerAppendedForest W).depth
      (printedGeneratedNormalizerAppendedForest W).tree) :
    cavityGeneratedForestTerminalProjection W.depth W.tree
      (printedGeneratedNormalizerOldRecord W.depth W.tree (printedGeneratedAppendRecordToNative W z)) =
    printedGeneratedNormalizerOldTerminalProjection W
      (cavityGeneratedForestTerminalProjection
        (printedGeneratedNormalizerAppendedForest W).depth
        (printedGeneratedNormalizerAppendedForest W).tree z) := by
  funext c
  change finiteCascadeRecordTerminalSpins (W.tree c)
    (cast (congrArg (PrintedGeneratedComponentRecord n)
      (printedGeneratedNormalizerAppendedForest_old_component W c)) (z c.castSucc)).2 = _
  exact componentTerminalCast_record (n:=n) _ _
    (printedGeneratedNormalizerAppendedForest_old_component W c) _

theorem printedGeneratedNormalizerFreshTerminalProjection_record
    (W : CavityGeneratedConstructedForest m)
    (z : CavityGeneratedForestRecord (n:=n)
      (printedGeneratedNormalizerAppendedForest W).depth
      (printedGeneratedNormalizerAppendedForest W).tree) :
    finiteCascadeRecordTerminalSpins anisotropicBinaryObservationTree
      (printedGeneratedNormalizerNewRecord W.depth W.tree (printedGeneratedAppendRecordToNative W z)).2 =
    printedGeneratedNormalizerFreshTerminalProjection W
      (cavityGeneratedForestTerminalProjection
        (printedGeneratedNormalizerAppendedForest W).depth
        (printedGeneratedNormalizerAppendedForest W).tree z) := by
  change finiteCascadeRecordTerminalSpins anisotropicBinaryObservationTree
    (cast (congrArg (PrintedGeneratedComponentRecord n)
      (printedGeneratedNormalizerAppendedForest_new_component W)) (z (Fin.last W.componentCount))).2 = _
  exact componentTerminalCast_record (n:=n) _ _
    (printedGeneratedNormalizerAppendedForest_new_component W) _

def printedGeneratedNormalizerPairSourceTest (W : CavityGeneratedConstructedForest m)
    (F : CavityGeneratedHistory Paper.Overlap m →
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (H : CavityGeneratedHistory Paper.Overlap (m+1))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (printedGeneratedNormalizerAppendedForest W).depth
      (printedGeneratedNormalizerAppendedForest W).tree) : ℝ :=
  F (H ∘ Fin.castSucc) (printedGeneratedNormalizerOldTerminalProjection W σ) *
    cavityGeneratedForestPairDefect n (printedGeneratedNormalizerAppendedForest W)
      (printedGeneratedNormalizerFreshPair W) H σ

def printedGeneratedNormalizerTaggedSuccessor (W : CavityGeneratedConstructedForest m)
    (A : CavityGeneratedTaggedTest n W d) :
    CavityGeneratedTaggedTest n (printedGeneratedNormalizerAppendedForest W) (d+1) where
  base := fun z => A.base (z.1 ∘ Fin.castSucc,printedGeneratedNormalizerOldTerminalProjection W z.2)
  pairs := Fin.snoc (fun i => printedGeneratedNormalizerOldPair W (A.pairs i))
    (printedGeneratedNormalizerFreshPair W)

theorem printedGeneratedNormalizerTaggedSuccessor_value
    (W : CavityGeneratedConstructedForest m) (A : CavityGeneratedTaggedTest n W d)
    (H : CavityGeneratedHistory Paper.Overlap (m+1))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (printedGeneratedNormalizerAppendedForest W).depth
      (printedGeneratedNormalizerAppendedForest W).tree) :
    cavityGeneratedTaggedTestValue (printedGeneratedNormalizerAppendedForest W)
      (printedGeneratedNormalizerTaggedSuccessor W A) (H,σ) =
    printedGeneratedNormalizerPairSourceTest W
      (fun h τ => cavityGeneratedTaggedTestValue W A (h,τ)) H σ := by
  unfold cavityGeneratedTaggedTestValue printedGeneratedNormalizerTaggedSuccessor
    printedGeneratedNormalizerPairSourceTest
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last,printedGeneratedNormalizerOldPair_defect]
  ring

theorem printedGeneratedNormalizerSourceExpectation_pair_test
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m)
    (F : CavityGeneratedHistory Paper.Overlap m →
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (H : CavityGeneratedHistory Paper.Overlap (m+1)) :
    printedGeneratedNormalizerSourceExpectation D μ a W F H =
      ∫σ,printedGeneratedNormalizerPairSourceTest W F H σ
        ∂(cavityGeneratedNativeForestTerminalProbability D μ a
          (printedGeneratedNormalizerAppendedForest W).depth
          (printedGeneratedNormalizerAppendedForest W).tree
          ((printedGeneratedNormalizerAppendedForest W).clockTemplate.clock H) : Measure _) := by
  unfold printedGeneratedNormalizerSourceExpectation
  calc
    _ = ∫z,printedGeneratedNormalizerPairSourceTest W F H
        (cavityGeneratedForestTerminalProjection
          (printedGeneratedNormalizerAppendedForest W).depth
          (printedGeneratedNormalizerAppendedForest W).tree z)
        ∂cavityGeneratedNativeForestLaw D μ a
          (printedGeneratedNormalizerAppendedForest W).depth
          (printedGeneratedNormalizerAppendedForest W).tree
          ((printedGeneratedNormalizerAppendedForest W).clockTemplate.clock H) := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro z
      unfold printedGeneratedNormalizerPairSourceTest
      dsimp only
      rw [printedGeneratedNormalizerFreshPair_defect,
        ←printedGeneratedNormalizerOldTerminalProjection_record,
        ←printedGeneratedNormalizerFreshTerminalProjection_record]
    _ = _ := cavityGeneratedNativeForest_integral_terminal D μ a
      (printedGeneratedNormalizerAppendedForest W).depth
      (printedGeneratedNormalizerAppendedForest W).tree
      ((printedGeneratedNormalizerAppendedForest W).clockTemplate.clock H) _

end QuantitativeFollowup
