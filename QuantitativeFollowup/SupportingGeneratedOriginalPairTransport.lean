module
public import QuantitativeFollowup.FollowupCavityGeneratedStreamingTaggedTests
public import QuantitativeFollowup.FollowupCavityGeneratedStreamingStepSourceCoverageOriginal

@[expose] public section

/-! The original source term appends its literal original leaf pair to
all prior tags. Repeated leaves give the actual zero diagonal defect. -/
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

def cavityGeneratedOriginalPair (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (i k : ObservationLeaf (W.tree c)) :
    CavityGeneratedForestPair W := ⟨c,i,k⟩

def cavityGeneratedOriginalTaggedTest (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (i k : ObservationLeaf (W.tree c))
    (A : CavityGeneratedTaggedTest n W d) : CavityGeneratedTaggedTest n W (d+1) where
  base := A.base
  pairs := Fin.snoc A.pairs (cavityGeneratedOriginalPair W c i k)

theorem cavityGeneratedOriginalPair_defect (hn : 0<n)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (i k : ObservationLeaf (W.tree c)) (h : CavityGeneratedHistory Paper.Overlap m)
    (σ : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree) :
    (if i=k then 0 else cavitySpinOverlapDefect n
      (W.clockTemplate.clock h c (observationCommonLevel (W.tree c) i k))
      (observationTerminalSpin (W.tree c) i (σ c))
      (observationTerminalSpin (W.tree c) k (σ c))) =
      cavityGeneratedForestPairDefect n W (cavityGeneratedOriginalPair W c i k) h σ := by
  by_cases hik : i=k
  · subst k
    simp only [if_pos rfl,cavityGeneratedForestPairDefect,cavityGeneratedOriginalPair,
      observationCommonLevel_self,W.clockTemplate.clock_terminal,Set.Icc.coe_one,cavitySpinOverlapDefect_self n hn,ite_true]
  · simp only [if_neg hik,cavityGeneratedForestPairDefect,cavityGeneratedOriginalPair]

theorem cavityGeneratedOriginalTaggedTest_receiver (hn : 0<n)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (i k : ObservationLeaf (W.tree c)) (A : CavityGeneratedTaggedTest n W d)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (σ : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree) :
    cavityGeneratedStreamingOriginalTest W c i k (cavityGeneratedTaggedTestValue W A) h σ =
      cavityGeneratedTaggedTestValue W (cavityGeneratedOriginalTaggedTest W c i k A) (h,σ) := by
  unfold cavityGeneratedStreamingOriginalTest
  rw [cavityGeneratedOriginalPair_defect hn]
  unfold cavityGeneratedTaggedTestValue cavityGeneratedOriginalTaggedTest
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last]
  ring

end QuantitativeFollowup
