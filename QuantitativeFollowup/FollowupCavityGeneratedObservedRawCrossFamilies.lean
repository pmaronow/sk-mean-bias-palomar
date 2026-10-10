module
public import QuantitativeFollowup.FollowupCavityGeneratedRawCrossComponent
public import QuantitativeFollowup.SupportingGeneratedObservedRawComponentLaw
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawLeafCounts

@[expose] public section

/-! A raw cross chart replaces exactly the selected original component.
All other components retain their actual trees and unary clocks. The
new support and two-leaf increase are consequences of the concrete
refinement and the two original-location grafts. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

def cavityGeneratedObservedRawCrossChartForest
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (k : NativeStreamingGeneratedCrossEdgeChart) : CavityGeneratedObservedRawForest (m+2) :=
  cavityGeneratedObservedRawForestReplaceComponent (W.reindex (fun i=>i.castSucc.castSucc)) c
    (cavityGeneratedObservedRawCrossComponent (W.component c)
      (cavityGeneratedRawCrossSite (W.tree c) γ) (cavityGeneratedRawCrossSite (W.tree c) δ) k)

theorem cavityGeneratedObservedRawCrossChartForest_selected
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (k : NativeStreamingGeneratedCrossEdgeChart) :
    (cavityGeneratedObservedRawCrossChartForest W c γ δ k).component c=
      cavityGeneratedObservedRawCrossComponent (W.component c)
        (cavityGeneratedRawCrossSite (W.tree c) γ) (cavityGeneratedRawCrossSite (W.tree c) δ) k :=
  cavityGeneratedObservedRawForestReplaceComponent_same _ _ _

theorem cavityGeneratedObservedRawCrossChartForest_other
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (k : NativeStreamingGeneratedCrossEdgeChart) (i : Fin W.componentCount) (hi : i≠c) :
    (cavityGeneratedObservedRawCrossChartForest W c γ δ k).component i=
      (W.component i).reindex (fun j=>j.castSucc.castSucc) :=
  cavityGeneratedObservedRawForestReplaceComponent_other _ _ _ _ hi

private def rawCrossFamilyLeafCount {M : ℕ} (U : CavityGeneratedObservedRawComponent M) : ℕ :=
  FiniteCascadeGenealogy.leafCount (asGenealogy U.tree)

private theorem rawCrossFamily_replace_leafCount {M : ℕ}
    (W : CavityGeneratedObservedRawForest M) (c : Fin W.componentCount)
    (U : CavityGeneratedObservedRawComponent M) :
    (cavityGeneratedObservedRawForestReplaceComponent W c U).leafCount+rawCrossFamilyLeafCount (W.component c)=
      W.leafCount+rawCrossFamilyLeafCount U :=
  cavityGeneratedObservedRawForestReplaceComponent_leafCount W c U

theorem cavityGeneratedObservedRawCrossChartForest_leafCount
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (k : NativeStreamingGeneratedCrossEdgeChart) :
    (cavityGeneratedObservedRawCrossChartForest W c γ δ k).leafCount=W.leafCount+2 := by
  have H := rawCrossFamily_replace_leafCount (W.reindex (fun i=>i.castSucc.castSucc)) c
    (cavityGeneratedObservedRawCrossComponent (W.component c)
      (cavityGeneratedRawCrossSite (W.tree c) γ) (cavityGeneratedRawCrossSite (W.tree c) δ) k)
  have Hc := cavityGeneratedObservedRawCrossComponent_leafCount (W.component c)
    (cavityGeneratedRawCrossSite (W.tree c) γ) (cavityGeneratedRawCrossSite (W.tree c) δ) k
  change (cavityGeneratedObservedRawCrossChartForest W c γ δ k).leafCount+
      rawCrossFamilyLeafCount (W.component c)=W.leafCount+_ at H
  change rawCrossFamilyLeafCount (cavityGeneratedObservedRawCrossComponent (W.component c)
      (cavityGeneratedRawCrossSite (W.tree c) γ) (cavityGeneratedRawCrossSite (W.tree c) δ) k)=
      rawCrossFamilyLeafCount (W.component c)+2 at Hc
  omega

theorem cavityGeneratedObservedRawCrossChartForest_support_append
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (k : NativeStreamingGeneratedCrossEdgeChart) (h : CavityGeneratedHistory Paper.Overlap m)
    (hh : h∈W.supportSet) (r l : Paper.Overlap)
    (hr : cavityGeneratedRawCrossCell (W.clock h c) (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) γ) r)
    (hl : cavityGeneratedRawCrossCell (W.clock h c) (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) δ) l)
    (hk : cavityGeneratedRawCrossChartHolds (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) γ)
      (cavityGeneratedRawCrossSite (W.tree c) δ) k r l)
    (hs : r=nativeStreamingOriginLevel (W.clock h c)
      (cavityGeneratedRawCrossOrigin (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) γ) r))
    (ht : l=nativeStreamingOriginLevel (W.clock h c)
      (cavityGeneratedRawCrossOrigin (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) δ) l)) :
    cavityGeneratedRawCrossAppend h r l∈(cavityGeneratedObservedRawCrossChartForest W c γ δ k).supportSet := by
  intro i
  by_cases hi : i=c
  · subst i
    rw [cavityGeneratedObservedRawCrossChartForest_selected]
    exact cavityGeneratedObservedRawCrossComponent_support (W.component c)
      (cavityGeneratedRawCrossSite (W.tree c) γ) (cavityGeneratedRawCrossSite (W.tree c) δ) k h
      (hh c) r l hr hl hk hs ht
  · rw [cavityGeneratedObservedRawCrossChartForest_other W c γ δ k i hi]
    change cavityGeneratedRawCrossPrefix (cavityGeneratedRawCrossAppend h r l)∈(W.component i).supportSet
    rw [cavityGeneratedRawCrossPrefix_append]
    exact hh i

end QuantitativeFollowup
