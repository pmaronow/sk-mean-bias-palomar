module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedSharedFuturePatternsHistory

@[expose] public section

/-! The literal strict-future branch receiver. Open cells and the strict
future mask remain explicit; equal adjacent clocks give an empty free
cell. Root and endpoint atoms belong to the separate genuine atom programs. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

def nativeStreamingGeneratedSharedFutureSourceOrderSet
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (e : NativeStreamingEdge W.tree) :
    Set (CavityGeneratedHistory Paper.Overlap m × Paper.Overlap) :=
  {z | nativeStreamingGeneratedComponentClock W z.1 (e.depth+1) < z.2 ∧
    z.2 < nativeStreamingGeneratedComponentClock W z.1 e.depth ∧
    nativeStreamingGeneratedComponentClock W z.1 v.depth < z.2}

theorem measurableSet_nativeStreamingGeneratedSharedFutureSourceOrderSet
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (e : NativeStreamingEdge W.tree) :
    MeasurableSet (nativeStreamingGeneratedSharedFutureSourceOrderSet W v e) := by
  have hlo : Continuous (fun z : CavityGeneratedHistory Paper.Overlap m × Paper.Overlap =>
      nativeStreamingGeneratedComponentClock W z.1 (e.depth+1)) :=
    (nativeStreamingGeneratedComponentClock_continuous W (e.depth+1)).comp continuous_fst
  have hhi : Continuous (fun z : CavityGeneratedHistory Paper.Overlap m × Paper.Overlap =>
      nativeStreamingGeneratedComponentClock W z.1 e.depth) :=
    (nativeStreamingGeneratedComponentClock_continuous W e.depth).comp continuous_fst
  have hv : Continuous (fun z : CavityGeneratedHistory Paper.Overlap m × Paper.Overlap =>
      nativeStreamingGeneratedComponentClock W z.1 v.depth) :=
    (nativeStreamingGeneratedComponentClock_continuous W v.depth).comp continuous_fst
  exact (isOpen_lt hlo continuous_snd).measurableSet.inter
    ((isOpen_lt continuous_snd hhi).measurableSet.inter
      (isOpen_lt hv continuous_snd).measurableSet)

theorem nativeStreamingGeneratedSharedFutureSourceOrderSet_section
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (e : NativeStreamingEdge W.tree)
    (h : CavityGeneratedHistory Paper.Overlap m) :
    {r | (h,r) ∈ nativeStreamingGeneratedSharedFutureSourceOrderSet W v e} =
      Ioo (nativeStreamingGeneratedComponentClock W h (e.depth+1))
        (nativeStreamingGeneratedComponentClock W h e.depth) ∩
        Ioi (nativeStreamingGeneratedComponentClock W h v.depth) := by
  ext r
  simp only [nativeStreamingGeneratedSharedFutureSourceOrderSet,Set.mem_setOf_eq,
    Set.mem_inter_iff,Set.mem_Ioo,Set.mem_Ioi]
  tauto

theorem nativeStreamingGeneratedSharedFutureSourceOrderSet_empty_of_repeated
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (e : NativeStreamingEdge W.tree)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (he : nativeStreamingGeneratedComponentClock W h (e.depth+1) =
      nativeStreamingGeneratedComponentClock W h e.depth) :
    {r | (h,r) ∈ nativeStreamingGeneratedSharedFutureSourceOrderSet W v e} = ∅ := by
  rw [nativeStreamingGeneratedSharedFutureSourceOrderSet_section,he]
  simp only [Ioo_self,empty_inter]

theorem nativeStreamingGeneratedSharedFutureBranchComponent_record_law_snoc
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (b : Fin m)
    (hb : cavityGeneratedFiniteClockLabels W.label v.depth = .mark b)
    (e : NativeStreamingEdge W.tree) (hj : e.depth < v.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet W)
    (hr : nativeStreamingGeneratedComponentClock W h (e.depth+1) ≤ r ∧
      r ≤ nativeStreamingGeneratedComponentClock W h e.depth) :
    (anisotropicRecordedProfileTreeLaw D μ a
      (nativeStreamingGeneratedComponentClock
        (nativeStreamingGeneratedSharedFutureBranchComponent W v b hb e hj)
        (Fin.snoc (Fin.snoc h (h b)) r))
      (nativeStreamingGeneratedSharedFutureBranchComponent W v b hb e hj).tree).map
        (nativeStreamingGeneratedSharedFutureRecordProject
          (nativeStreamingGeneratedSharedFutureBranchBase W) v b.castSucc
          (nativeStreamingGeneratedSharedFutureBranchBase_label W v b hb) e hj) =
      (nativeStreamingOriginFutureProbability D μ a (nativeStreamingGeneratedComponentClock W h)
        W.tree (.vertex v) e.depth r : Measure
          ((AnisotropicObservationState n ×
            Records (AnisotropicObservationState n) (Configuration n) W.tree) ×
              (Configuration n × Configuration n))) := by
  have hbase : Fin.snoc h (h b) ∈ nativeStreamingGeneratedComponentOrderSet
      (nativeStreamingGeneratedSharedFutureBranchBase W) := by
    rw [nativeStreamingGeneratedSharedFutureBranchBase_order,cavityGeneratedHistoryPrefix_snoc]
    exact hh
  have hc : nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedSharedFutureBranchBase W)
      (Fin.snoc h (h b)) = nativeStreamingGeneratedComponentClock W h := by
    rw [nativeStreamingGeneratedSharedFutureBranchBase_clock,cavityGeneratedHistoryPrefix_snoc]
  have hx := nativeStreamingGeneratedSharedFutureComponent_record_law D μ a
    (nativeStreamingGeneratedSharedFutureBranchBase W) v b.castSucc
    (nativeStreamingGeneratedSharedFutureBranchBase_label W v b hb) e hj
    (Fin.snoc h (h b)) r hbase (by simpa only [hc] using hr)
  rw [hc] at hx
  exact hx

theorem nativeStreamingGeneratedSharedFutureBranchComponent_leafCount
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (b : Fin m)
    (hb : cavityGeneratedFiniteClockLabels W.label v.depth = .mark b)
    (e : NativeStreamingEdge W.tree) (hj : e.depth < v.depth) :
    FiniteCascadeGenealogy.leafCount
        (asGenealogy (nativeStreamingGeneratedSharedFutureBranchComponent W v b hb e hj).tree) =
      FiniteCascadeGenealogy.leafCount (asGenealogy W.tree) + 2 := by
  change FiniteCascadeGenealogy.leafCount (asGenealogy
    (finiteCascadeFutureVertexGraft
      (nativeStreamingGeneratedSharedFutureAnchor (nativeStreamingGeneratedSharedFutureBranchBase W) v e)
      (e.depth+1))) = _
  rw [finiteCascadeFutureVertexGraft_leafCount]
  exact congrArg (fun L : ℕ => L+2)
    (leafCount_observationRefineTree (nativeStreamingEdgeSubdivision e.depth) W.tree)

theorem nativeStreamingGeneratedSharedFutureBranchMoment_eq_constructed_integral
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (b : Fin m)
    (hb : cavityGeneratedFiniteClockLabels W.label v.depth = .mark b)
    (e : NativeStreamingEdge W.tree) (hj : e.depth < v.depth)
    (F : CavityGeneratedHistory Paper.Overlap m → TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet W)
    (hr : nativeStreamingGeneratedComponentClock W h (e.depth+1) ≤ r ∧
      r ≤ nativeStreamingGeneratedComponentClock W h e.depth) :
    nativeStreamingGeneratedSharedFutureBranchMoment D μ a W v e F
      (Fin.snoc (Fin.snoc h (h b)) r) =
    ∫z, let R := (nativeStreamingGeneratedSharedFutureRecordProject (n:=n+1)
        (nativeStreamingGeneratedSharedFutureBranchBase W) v b.castSucc
        (nativeStreamingGeneratedSharedFutureBranchBase_label W v b hb) e hj z)
      nativeStreamingDefectSpinTest W.tree (F h) r
        (finiteCascadeRecordTerminalSpins W.tree R.1.2,R.2)
      ∂anisotropicRecordedProfileTreeLaw D μ a
        (nativeStreamingGeneratedComponentClock
          (nativeStreamingGeneratedSharedFutureBranchComponent W v b hb e hj)
          (Fin.snoc (Fin.snoc h (h b)) r))
        (nativeStreamingGeneratedSharedFutureBranchComponent W v b hb e hj).tree := by
  let test := fun z : (AnisotropicObservationState (n+1) ×
      Records (AnisotropicObservationState (n+1)) (Configuration (n+1)) W.tree) ×
        (Configuration (n+1) × Configuration (n+1)) =>
      nativeStreamingDefectSpinTest W.tree (F h) r
        (finiteCascadeRecordTerminalSpins W.tree z.1.2,z.2)
  have ht : Measurable test := (continuous_of_discreteTopology
      (f:=nativeStreamingDefectSpinTest W.tree (F h) r)).measurable.comp
        (((measurable_finiteCascadeRecordTerminalSpins W.tree).comp
          measurable_fst.snd).prodMk measurable_snd)
  have he := congrArg (fun L : Measure ((AnisotropicObservationState (n+1) ×
      Records (AnisotropicObservationState (n+1)) (Configuration (n+1)) W.tree) ×
        (Configuration (n+1) × Configuration (n+1))) => ∫z, test z ∂L)
    (nativeStreamingGeneratedSharedFutureBranchComponent_record_law_snoc D μ a W v b hb e hj h r hh hr)
  have hi := integral_map
    (μ:=anisotropicRecordedProfileTreeLaw D μ a
      (nativeStreamingGeneratedComponentClock
        (nativeStreamingGeneratedSharedFutureBranchComponent W v b hb e hj)
        (Fin.snoc (Fin.snoc h (h b)) r))
      (nativeStreamingGeneratedSharedFutureBranchComponent W v b hb e hj).tree)
    (measurable_nativeStreamingGeneratedSharedFutureRecordProject
      (n:=n+1) (nativeStreamingGeneratedSharedFutureBranchBase W) v b.castSucc
      (nativeStreamingGeneratedSharedFutureBranchBase_label W v b hb) e hj).aemeasurable
    ht.aestronglyMeasurable
  have hs : nativeStreamingGeneratedSharedFutureBranchMoment D μ a W v e F
      (Fin.snoc (Fin.snoc h (h b)) r) =
      nativeStreamingPatternMoment D μ a (nativeStreamingGeneratedComponentClock W h)
        W.tree (F h) (.future (.vertex v) e.depth r) := by
    unfold nativeStreamingGeneratedSharedFutureBranchMoment
    rw [nativeStreamingGeneratedSharedFutureHistoryEraseBranch_snoc,cavityGeneratedHistoryPrefix_snoc]
    exact nativeStreamingGeneratedSharedFutureMoment_snoc D μ a W v e F h r hh hr
  exact hs.trans (he.symm.trans hi)

theorem nativeStreamingGeneratedSharedFutureBranchComponent_pair_common_clock
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (b : Fin m)
    (hb : cavityGeneratedFiniteClockLabels W.label v.depth = .mark b)
    (e : NativeStreamingEdge W.tree) (hj : e.depth < v.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet W)
    (hr : nativeStreamingGeneratedComponentClock W h (e.depth+1) ≤ r ∧
      r ≤ nativeStreamingGeneratedComponentClock W h e.depth) :
    let V := nativeStreamingGeneratedSharedFutureAnchor (nativeStreamingGeneratedSharedFutureBranchBase W) v e
    let P := finiteCascadeFuturePairTree (e.depth+1) V.depth
    nativeStreamingGeneratedComponentClock
      (nativeStreamingGeneratedSharedFutureBranchComponent W v b hb e hj)
      (Fin.snoc (Fin.snoc h (h b)) r)
      (observationCommonLevel P.tree (observationPairFirstLeaf P) (observationPairSecondLeaf P)) = r := by
  dsimp only
  rw [observationPair_commonLevel,
    finiteCascadeFuturePairTree_split _ _
      (nativeStreamingGeneratedSharedFuture_split_le_anchor
        (nativeStreamingGeneratedSharedFutureBranchBase W) v e hj)]
  have hbase : Fin.snoc h (h b) ∈ nativeStreamingGeneratedComponentOrderSet
      (nativeStreamingGeneratedSharedFutureBranchBase W) := by
    rw [nativeStreamingGeneratedSharedFutureBranchBase_order,cavityGeneratedHistoryPrefix_snoc]
    exact hh
  have hc : nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedSharedFutureBranchBase W)
      (Fin.snoc h (h b)) = nativeStreamingGeneratedComponentClock W h := by
    rw [nativeStreamingGeneratedSharedFutureBranchBase_clock,cavityGeneratedHistoryPrefix_snoc]
  exact nativeStreamingGeneratedSharedFuture_split_clock
    (nativeStreamingGeneratedSharedFutureBranchBase W) v b.castSucc
    (nativeStreamingGeneratedSharedFutureBranchBase_label W v b hb) e hj
    (Fin.snoc h (h b)) r hbase (by simpa only [hc] using hr)

theorem nativeStreamingGeneratedSharedFuture_source_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ) (ha : 0 ≤ a)
    (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (W : CavityGeneratedConstructedComponent m)
    (v : FiniteCascadeRecordVertex W.tree) (b : Fin m)
    (hb : cavityGeneratedFiniteClockLabels W.label v.depth = .mark b)
    (e : NativeStreamingEdge W.tree) (hj : e.depth < v.depth)
    (l : ℕ) (hl : 1 ≤ l)
    (F : CavityGeneratedHistory Paper.Overlap m → TerminalSpins (Configuration (n+1)) W.tree → ℝ)
    (hF : ∀σ, Continuous (fun h => F h σ))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀h σ, |F h σ| ≤ C) :
    (∫H, nativeStreamingGeneratedSharedFutureBranchMoment D μ a W v e F H
      ∂(nativeStreamingGeneratedSharedFutureProgram μ P W b l
        (nativeStreamingGeneratedSharedFutureSourceOrderSet W v e)).measure (parisiFreeMeasure μ a)) =
    ∫h, nativeStreamingBranchCharge μ a (nativeStreamingGeneratedComponentClock W h v.depth) l *
      (∫r, nativeStreamingPatternMoment D μ a (nativeStreamingGeneratedComponentClock W h)
        W.tree (F h) (.future (.vertex v) e.depth r)
        ∂(parisiFreeMeasure μ a).restrict
          (Ioo (nativeStreamingGeneratedComponentClock W h (e.depth+1))
            (nativeStreamingGeneratedComponentClock W h e.depth) ∩
              Ioi (nativeStreamingGeneratedComponentClock W h v.depth)))
      ∂(P.measure (parisiFreeMeasure μ a)).restrict (nativeStreamingGeneratedComponentOrderSet W) := by
  have he := nativeStreamingGeneratedSharedFuture_restricted_receiver D μ a ha P W v b hb e l hl
    (nativeStreamingGeneratedSharedFutureSourceOrderSet W v e)
    (measurableSet_nativeStreamingGeneratedSharedFutureSourceOrderSet W v e)
    (fun z hz => ⟨hz.1.le,hz.2.1.le⟩) F hF C hC hbound
  simpa only [nativeStreamingGeneratedSharedFutureSourceOrderSet_section] using he

end QuantitativeFollowup
