module
public import QuantitativeFollowup.FollowupCavityGeneratedFutureOriginFamilies
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedEndpointVertexPatternsLaw

@[expose] public section

/-! Actual projections of the canonical future chart outputs retain the
complete original observation record and the two literal fresh spins. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

def printedGeneratedFutureVertexRecordProject
    (U : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex U.tree)
    (hv0 : 0 < v.depth) (hvJ : v.depth < U.depth) (j : ℕ) (hj : j < v.depth) :
    PrintedGeneratedComponentRecord n (printedGeneratedFutureVertexComponent U v hv0 hvJ j hj) →
      PrintedGeneratedComponentRecord n U × (Configuration (n+1) × Configuration (n+1)) :=
  nativeStreamingGeneratedSharedFutureRecordProject
    (printedGeneratedFutureVertexBase U v hv0 hvJ) v (Fin.last m)
    (printedGeneratedFutureVertexBase_label U v hv0 hvJ)
    (printedGeneratedFutureCellEdge (printedGeneratedFutureVertexBase U v hv0 hvJ) j (hj.trans hvJ))
    (by rw [printedGeneratedFutureCellEdge_depth]; exact hj)

theorem measurable_printedGeneratedFutureVertexRecordProject
    (U : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex U.tree)
    (hv0 : 0 < v.depth) (hvJ : v.depth < U.depth) (j : ℕ) (hj : j < v.depth) :
    Measurable (printedGeneratedFutureVertexRecordProject (n:=n) U v hv0 hvJ j hj) :=
  measurable_nativeStreamingGeneratedSharedFutureRecordProject _ _ _ _ _ _

theorem printedGeneratedFutureVertexRecordProject_law
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (U : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex U.tree)
    (hv0 : 0 < v.depth) (hvJ : v.depth < U.depth) (j : ℕ) (hj : j < v.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) (l : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hl : nativeStreamingGeneratedComponentClock U h (j+1) ≤ l ∧
      l ≤ nativeStreamingGeneratedComponentClock U h j) :
    (printedGeneratedComponentLaw D μ a (printedGeneratedFutureVertexComponent U v hv0 hvJ j hj)
      (nativeStreamingGeneratedCrossEdgeAppend h (nativeStreamingGeneratedComponentClock U h v.depth) l)).map
        (printedGeneratedFutureVertexRecordProject U v hv0 hvJ j hj) =
      (nativeStreamingOriginFutureProbability D μ a (nativeStreamingGeneratedComponentClock U h)
        U.tree (.vertex v) j l : Measure _) := by
  let B := printedGeneratedFutureVertexBase U v hv0 hvJ
  let e := printedGeneratedFutureCellEdge B j (hj.trans hvJ)
  let H : CavityGeneratedHistory Paper.Overlap (m+1) :=
    Fin.snoc h (nativeStreamingGeneratedComponentClock U h v.depth)
  have he : e.depth = j := printedGeneratedFutureCellEdge_depth B j (hj.trans hvJ)
  have hB : H ∈ nativeStreamingGeneratedComponentOrderSet B :=
    printedGeneratedFutureVertexBase_snoc_order U v hv0 hvJ h hh
  have hclock : nativeStreamingGeneratedComponentClock B H = nativeStreamingGeneratedComponentClock U h :=
    printedGeneratedFutureVertexBase_clock_snoc U v hv0 hvJ h hh
  have hlB : nativeStreamingGeneratedComponentClock B H (e.depth+1) ≤ l ∧
      l ≤ nativeStreamingGeneratedComponentClock B H e.depth := by
    rw [hclock,he]
    exact hl
  have hx := nativeStreamingGeneratedSharedFutureComponent_record_law D μ a B v (Fin.last m)
    (printedGeneratedFutureVertexBase_label U v hv0 hvJ) e
    (by rw [he]; exact hj) H l hB hlB
  have hright : (nativeStreamingOriginFutureProbability D μ a
      (nativeStreamingGeneratedComponentClock B H) B.tree (.vertex v) e.depth l).toMeasure =
      (nativeStreamingOriginFutureProbability D μ a (nativeStreamingGeneratedComponentClock U h)
        U.tree (.vertex v) j l).toMeasure := by
    rw [hclock]
    exact congrArg (fun p => (nativeStreamingOriginFutureProbability D μ a
      (nativeStreamingGeneratedComponentClock U h) U.tree (.vertex v) p l).toMeasure) he
  unfold printedGeneratedComponentLaw
  rw [printedGeneratedComponentClock_eq_native]
  exact hx.trans hright

def printedGeneratedFutureOriginChartOrigin
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (r : Paper.Overlap) : NativeStreamingOrigin U.tree := match γ with
  | .inl i => .vertex (printedGeneratedOriginChartFork U i)
  | .inr (.inl i) => .edge (printedGeneratedOriginChartEdge U i) r
  | .inr (.inr _) => .vertex (.root U.tree)

def printedGeneratedFutureOriginChartRecordProject
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U) (j : Fin U.depth) :
    PrintedGeneratedComponentRecord n (printedGeneratedOriginFutureChartComponent U γ j) →
      PrintedGeneratedComponentRecord n U × (Configuration (n+1) × Configuration (n+1)) :=
  match γ with
  | .inl i =>
      let v := printedGeneratedOriginChartFork U i
      let hv := printedGeneratedOriginChartFork_interior U i
      printedGeneratedFutureVertexRecordProject U v hv.1 hv.2 (min j.val (v.depth-1))
        (Nat.lt_of_le_of_lt (Nat.min_le_right j.val (v.depth-1)) (Nat.sub_lt hv.1 Nat.one_pos))
  | .inr (.inl i) => nativeStreamingGeneratedSharedFutureEdgeRecordProject U
      (printedGeneratedOriginChartEdge U i) (min j.val (printedGeneratedOriginChartEdge U i).depth)
      (Nat.min_le_right _ _)
  | .inr (.inr _) => fun z =>
      let B := nativeStreamingGeneratedEndpointComponent U
      let v := nativeStreamingGeneratedEndpointVertex U (.root U.tree)
      let hv := nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)
      let x := printedGeneratedFutureVertexRecordProject B v hv.1 hv.2 (j.val+1)
        (by rw [nativeStreamingGeneratedEndpointVertex_depth]; change j.val+1 < U.depth+1; omega) z
      ((x.1.1,nativeStreamingGeneratedEndpointRecordProject U x.1.2),x.2)

theorem measurable_printedGeneratedFutureOriginChartRecordProject
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U) (j : Fin U.depth) :
    Measurable (printedGeneratedFutureOriginChartRecordProject (n:=n) U γ j) := by
  rcases γ with i | (i | u)
  · let v := printedGeneratedOriginChartFork U i
    have hv := printedGeneratedOriginChartFork_interior U i
    exact measurable_printedGeneratedFutureVertexRecordProject U v hv.1 hv.2 _
      (Nat.lt_of_le_of_lt (Nat.min_le_right j.val (v.depth-1)) (Nat.sub_lt hv.1 Nat.one_pos))
  · exact measurable_nativeStreamingGeneratedSharedFutureEdgeRecordProject _ _ _ _
  · have hp := measurable_printedGeneratedFutureVertexRecordProject (n:=n)
      (nativeStreamingGeneratedEndpointComponent U) (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
      (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2 (j.val+1)
      (by rw [nativeStreamingGeneratedEndpointVertex_depth]; change j.val+1 < U.depth+1; omega)
    have hr := measurable_nativeStreamingGeneratedEndpointRecordProject
      (E:=AnisotropicObservationState (n+1)) (S:=Configuration (n+1)) U
    exact (hp.fst.fst.prodMk (hr.comp hp.fst.snd)).prodMk hp.snd

end QuantitativeFollowup
