module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawCrossProjection

@[expose] public section

/-! A computed raw cross successor preserves every old physical pair and
adds exactly its two fresh terminal leaves. The full base observable is
pulled back globally; only old-pair clock transport needs the source cells. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n d : ℕ}

def rawCrossLeafCast {M : ℕ} (U V : CavityGeneratedObservedRawComponent M)
    (he : U=V) (i : ObservationLeaf U.tree) : ObservationLeaf V.tree :=
  cast (congrArg (fun A : CavityGeneratedObservedRawComponent M=>ObservationLeaf A.tree) he) i

private def rawCrossComponentDefect {M : ℕ} (U : CavityGeneratedObservedRawComponent M)
    (H : CavityGeneratedHistory Paper.Overlap M) (i j : ObservationLeaf U.tree)
    (σ : CavityGeneratedObservedRawComponentTerminal n U) : ℝ :=
  cavitySpinOverlapDefect n (U.clock H (observationCommonLevel U.tree i j))
    (observationTerminalSpin U.tree i σ) (observationTerminalSpin U.tree j σ)

private theorem rawCrossLeafCast_defect {M : ℕ} (U V : CavityGeneratedObservedRawComponent M)
    (he : U=V) (H : CavityGeneratedHistory Paper.Overlap M) (i j : ObservationLeaf U.tree)
    (σ : CavityGeneratedObservedRawComponentTerminal n V) :
    rawCrossComponentDefect U H i j
      ((cavityGeneratedObservedRawComponentTerminalCastEquiv (n:=n) U V he).symm σ)=
      rawCrossComponentDefect V H (rawCrossLeafCast U V he i) (rawCrossLeafCast U V he j) σ := by
  cases he
  rfl

def cavityGeneratedObservedRawCrossPairMap
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (t : CavityGeneratedObservedRawPair W) :
    CavityGeneratedObservedRawPair (cavityGeneratedObservedRawCrossChartForest W c γ δ k) := by
  classical
  let V := W.reindex (fun i=>i.castSucc.castSucc)
  let U := cavityGeneratedObservedRawCrossComponent (W.component c)
    (cavityGeneratedRawCrossSite (W.tree c) γ) (cavityGeneratedRawCrossSite (W.tree c) δ) k
  rcases t with ⟨s,i,j⟩
  by_cases hs : s=c
  · subst s
    exact ⟨c,rawCrossLeafCast U _ (cavityGeneratedObservedRawForestReplaceComponent_same V c U).symm
        (cavityGeneratedRawCrossOldLeaf (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) γ)
          (cavityGeneratedRawCrossSite (W.tree c) δ) k i),
      rawCrossLeafCast U _ (cavityGeneratedObservedRawForestReplaceComponent_same V c U).symm
        (cavityGeneratedRawCrossOldLeaf (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) γ)
          (cavityGeneratedRawCrossSite (W.tree c) δ) k j)⟩
  · exact ⟨s,rawCrossLeafCast (V.component s) _
        (cavityGeneratedObservedRawForestReplaceComponent_other V c U s hs).symm i,
      rawCrossLeafCast (V.component s) _
        (cavityGeneratedObservedRawForestReplaceComponent_other V c U s hs).symm j⟩

def cavityGeneratedObservedRawCrossFreshPair
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedCrossEdgeChart) :
    CavityGeneratedObservedRawPair (cavityGeneratedObservedRawCrossChartForest W c γ δ k) :=
  let V := W.reindex (fun i=>i.castSucc.castSucc)
  let U := cavityGeneratedObservedRawCrossComponent (W.component c)
    (cavityGeneratedRawCrossSite (W.tree c) γ) (cavityGeneratedRawCrossSite (W.tree c) δ) k
  ⟨c,rawCrossLeafCast U _ (cavityGeneratedObservedRawForestReplaceComponent_same V c U).symm
      (cavityGeneratedRawCrossFirstLeaf (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) γ)
        (cavityGeneratedRawCrossSite (W.tree c) δ) k),
    rawCrossLeafCast U _ (cavityGeneratedObservedRawForestReplaceComponent_same V c U).symm
      (cavityGeneratedRawCrossSecondLeaf (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) γ)
        (cavityGeneratedRawCrossSite (W.tree c) δ) k)⟩

theorem cavityGeneratedObservedRawCrossPairMap_defect
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hr : cavityGeneratedRawCrossCell (W.clock h c) (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) γ) r)
    (hl : cavityGeneratedRawCrossCell (W.clock h c) (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) δ) l)
    (t : CavityGeneratedObservedRawPair W)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawCrossChartForest W c γ δ k).depth
      (cavityGeneratedObservedRawCrossChartForest W c γ δ k).tree) :
    cavityGeneratedObservedRawPairDefect W t h (cavityGeneratedObservedRawCrossOldTerminal W c γ δ k σ)=
      cavityGeneratedObservedRawPairDefect (cavityGeneratedObservedRawCrossChartForest W c γ δ k)
        (cavityGeneratedObservedRawCrossPairMap W c γ δ k t) (cavityGeneratedRawCrossAppend h r l) σ := by
  classical
  let V := W.reindex (fun i=>i.castSucc.castSucc)
  let U := cavityGeneratedObservedRawCrossComponent (W.component c)
    (cavityGeneratedRawCrossSite (W.tree c) γ) (cavityGeneratedRawCrossSite (W.tree c) δ) k
  let N := cavityGeneratedObservedRawCrossChartForest W c γ δ k
  let H := cavityGeneratedRawCrossAppend h r l
  rcases t with ⟨s,i,j⟩
  by_cases hs : s=c
  · subst s
    let τ := (cavityGeneratedObservedRawForestReplacementSelectedEquiv (n:=n) V c U).symm (σ c)
    have ho : cavityGeneratedObservedRawCrossOldTerminal W c γ δ k σ c=
        (cavityGeneratedRawCrossTerminalProjection (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) γ)
          (cavityGeneratedRawCrossSite (W.tree c) δ) k τ).1 := by
      simp only [cavityGeneratedObservedRawCrossOldTerminal,dif_pos rfl]
      rfl
    have hp := cavityGeneratedObservedRawCross_old_pair_defect (W.component c)
      (cavityGeneratedRawCrossSite (W.tree c) γ) (cavityGeneratedRawCrossSite (W.tree c) δ) k h r l hr hl i j τ
    have he := rawCrossLeafCast_defect U (N.component c)
      (cavityGeneratedObservedRawForestReplaceComponent_same V c U).symm H
      (cavityGeneratedRawCrossOldLeaf (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) γ)
        (cavityGeneratedRawCrossSite (W.tree c) δ) k i)
      (cavityGeneratedRawCrossOldLeaf (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) γ)
        (cavityGeneratedRawCrossSite (W.tree c) δ) k j) (σ c)
    change cavitySpinOverlapDefect n ((W.component c).clock h (observationCommonLevel (W.tree c) i j))
      (observationTerminalSpin (W.tree c) i (cavityGeneratedObservedRawCrossOldTerminal W c γ δ k σ c))
      (observationTerminalSpin (W.tree c) j (cavityGeneratedObservedRawCrossOldTerminal W c γ δ k σ c))=_
    rw [ho]
    have hm : cavityGeneratedObservedRawCrossPairMap W c γ δ k ⟨c,i,j⟩=
        (⟨c,rawCrossLeafCast U (N.component c)
          (cavityGeneratedObservedRawForestReplaceComponent_same V c U).symm
          (cavityGeneratedRawCrossOldLeaf (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) γ)
            (cavityGeneratedRawCrossSite (W.tree c) δ) k i),
          rawCrossLeafCast U (N.component c) (cavityGeneratedObservedRawForestReplaceComponent_same V c U).symm
          (cavityGeneratedRawCrossOldLeaf (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) γ)
            (cavityGeneratedRawCrossSite (W.tree c) δ) k j)⟩ : CavityGeneratedObservedRawPair N) := by
      simp only [cavityGeneratedObservedRawCrossPairMap,dif_pos rfl]
      rfl
    rw [hm]
    exact hp.trans he
  · have ho : cavityGeneratedObservedRawCrossOldTerminal W c γ δ k σ s=
        (cavityGeneratedObservedRawForestReplacementOtherEquiv (n:=n) V c U s hs).symm (σ s) := by
      simp only [cavityGeneratedObservedRawCrossOldTerminal,dif_neg hs]
      rfl
    have hc : (V.component s).clock H=(W.component s).clock h := by
      change (W.component s).clock (cavityGeneratedRawCrossPrefix H)=_
      rw [cavityGeneratedRawCrossPrefix_append]
    have he := rawCrossLeafCast_defect (V.component s) (N.component s)
      (cavityGeneratedObservedRawForestReplaceComponent_other V c U s hs).symm H i j (σ s)
    change cavitySpinOverlapDefect n ((W.component s).clock h (observationCommonLevel (W.tree s) i j))
      (observationTerminalSpin (W.tree s) i (cavityGeneratedObservedRawCrossOldTerminal W c γ δ k σ s))
      (observationTerminalSpin (W.tree s) j (cavityGeneratedObservedRawCrossOldTerminal W c γ δ k σ s))=_
    rw [ho,←hc]
    have hm : cavityGeneratedObservedRawCrossPairMap W c γ δ k ⟨s,i,j⟩=
        (⟨s,rawCrossLeafCast (V.component s) (N.component s)
          (cavityGeneratedObservedRawForestReplaceComponent_other V c U s hs).symm i,
          rawCrossLeafCast (V.component s) (N.component s)
          (cavityGeneratedObservedRawForestReplaceComponent_other V c U s hs).symm j⟩ : CavityGeneratedObservedRawPair N) := by
      simp only [cavityGeneratedObservedRawCrossPairMap,dif_neg hs]
      rfl
    rw [hm]
    exact he

theorem cavityGeneratedObservedRawCrossFreshPair_defect
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (H : CavityGeneratedHistory Paper.Overlap (m+2))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawCrossChartForest W c γ δ k).depth
      (cavityGeneratedObservedRawCrossChartForest W c γ δ k).tree) :
    cavityGeneratedObservedRawCrossFreshDefect W c γ δ k H σ=
      cavityGeneratedObservedRawPairDefect (cavityGeneratedObservedRawCrossChartForest W c γ δ k)
        (cavityGeneratedObservedRawCrossFreshPair W c γ δ k) H σ :=
  rawCrossLeafCast_defect _ _
    (cavityGeneratedObservedRawForestReplaceComponent_same (W.reindex (fun i=>i.castSucc.castSucc)) c _).symm H _ _ (σ c)

def cavityGeneratedObservedRawCrossTaggedTest
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (A : CavityGeneratedObservedRawTaggedTest n W d) :
    CavityGeneratedObservedRawTaggedTest n (cavityGeneratedObservedRawCrossChartForest W c γ δ k) (d+1) where
  base := fun z=>A.base (cavityGeneratedRawCrossPrefix z.1,cavityGeneratedObservedRawCrossOldTerminal W c γ δ k z.2)
  pairs := Fin.snoc (fun i=>cavityGeneratedObservedRawCrossPairMap W c γ δ k (A.pairs i))
    (cavityGeneratedObservedRawCrossFreshPair W c γ δ k)

theorem cavityGeneratedObservedRawCrossTaggedTest_receiver
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (A : CavityGeneratedObservedRawTaggedTest n W d)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hr : cavityGeneratedRawCrossCell (W.clock h c) (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) γ) r)
    (hl : cavityGeneratedRawCrossCell (W.clock h c) (W.tree c) (cavityGeneratedRawCrossSite (W.tree c) δ) l)
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawCrossChartForest W c γ δ k).depth
      (cavityGeneratedObservedRawCrossChartForest W c γ δ k).tree) :
    cavityGeneratedObservedRawCrossTest W c γ δ k (cavityGeneratedObservedRawTaggedValue W A)
      (cavityGeneratedRawCrossAppend h r l) σ=
      cavityGeneratedObservedRawTaggedValue (cavityGeneratedObservedRawCrossChartForest W c γ δ k)
        (cavityGeneratedObservedRawCrossTaggedTest W c γ δ k A) (cavityGeneratedRawCrossAppend h r l,σ) := by
  unfold cavityGeneratedObservedRawCrossTest cavityGeneratedObservedRawTaggedValue cavityGeneratedObservedRawCrossTaggedTest
  simp only [Fin.prod_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last,cavityGeneratedRawCrossPrefix_append]
  rw [cavityGeneratedObservedRawCrossFreshPair_defect]
  have hp : (∏ i, cavityGeneratedObservedRawPairDefect W (A.pairs i) h
      (cavityGeneratedObservedRawCrossOldTerminal W c γ δ k σ)) =
      ∏ i, cavityGeneratedObservedRawPairDefect
        (cavityGeneratedObservedRawCrossChartForest W c γ δ k)
        (cavityGeneratedObservedRawCrossPairMap W c γ δ k (A.pairs i))
        (cavityGeneratedRawCrossAppend h r l) σ := by
    apply Finset.prod_congr rfl
    intro i hi
    exact cavityGeneratedObservedRawCrossPairMap_defect W c γ δ k h r l hr hl (A.pairs i) σ
  rw [hp]
  exact mul_assoc _ _ _

theorem measurable_cavityGeneratedObservedRawCrossTaggedTest_base
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (A : CavityGeneratedObservedRawTaggedTest n W d) (hA : Measurable A.base) :
    Measurable (cavityGeneratedObservedRawCrossTaggedTest W c γ δ k A).base :=
  hA.comp (measurable_cavityGeneratedObservedRawCrossBaseMap W c γ δ k)

theorem cavityGeneratedObservedRawCrossTaggedTest_base_abs_le
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (A : CavityGeneratedObservedRawTaggedTest n W d) (L : ℝ)
    (hbound : ∀z, |A.base z|≤L) :
    ∀z, |(cavityGeneratedObservedRawCrossTaggedTest W c γ δ k A).base z|≤L :=
  fun z=>hbound _

end QuantitativeFollowup
