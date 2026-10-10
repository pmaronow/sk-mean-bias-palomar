module
public import QuantitativeFollowup.SupportingGeneratedObservedRawTaggedBounds
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawStreamingStepSourceCoverageOriginal

@[expose] public section

/-! The original source appends its genuine old leaf pair. The source's
diagonal is the literal zero physical defect, rather than an exclusion. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n m d : ℕ}
attribute [local instance] Classical.propDecidable

def cavityGeneratedObservedRawOriginalPair (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (i k : ObservationLeaf (W.tree c)) :
    CavityGeneratedObservedRawPair W := ⟨c,i,k⟩

def cavityGeneratedObservedRawOriginalTaggedTest (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (i k : ObservationLeaf (W.tree c))
    (A : CavityGeneratedObservedRawTaggedTest n W d) :
    CavityGeneratedObservedRawTaggedTest n W (d+1) where
  base := A.base
  pairs := Fin.snoc A.pairs (cavityGeneratedObservedRawOriginalPair W c i k)

theorem cavityGeneratedObservedRawOriginalPair_defect (hn : 0<n)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (i k : ObservationLeaf (W.tree c)) (h : CavityGeneratedHistory Paper.Overlap m)
    (σ : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree) :
    (if i=k then 0 else cavitySpinOverlapDefect n
      (W.clock h c (observationCommonLevel (W.tree c) i k))
      (observationTerminalSpin (W.tree c) i (σ c))
      (observationTerminalSpin (W.tree c) k (σ c))) =
      cavityGeneratedObservedRawPairDefect W (cavityGeneratedObservedRawOriginalPair W c i k) h σ := by
  by_cases hik : i=k
  · subst k
    simp only [if_pos rfl,cavityGeneratedObservedRawPairDefect,cavityGeneratedObservedRawOriginalPair,
      observationCommonLevel_self,W.clock_terminal,Set.Icc.coe_one,cavitySpinOverlapDefect_self n hn,ite_true]
  · simp only [if_neg hik,cavityGeneratedObservedRawPairDefect,cavityGeneratedObservedRawOriginalPair]

theorem cavityGeneratedObservedRawOriginalTaggedTest_receiver (hn : 0<n)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (i k : ObservationLeaf (W.tree c)) (A : CavityGeneratedObservedRawTaggedTest n W d)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (σ : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree) :
    cavityGeneratedObservedRawStreamingOriginalTest W c i k (cavityGeneratedObservedRawTaggedValue W A) h σ =
      cavityGeneratedObservedRawTaggedValue W (cavityGeneratedObservedRawOriginalTaggedTest W c i k A) (h,σ) := by
  unfold cavityGeneratedObservedRawStreamingOriginalTest
  rw [cavityGeneratedObservedRawOriginalPair_defect hn]
  unfold cavityGeneratedObservedRawTaggedValue cavityGeneratedObservedRawOriginalTaggedTest
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last]
  ring

end QuantitativeFollowup
