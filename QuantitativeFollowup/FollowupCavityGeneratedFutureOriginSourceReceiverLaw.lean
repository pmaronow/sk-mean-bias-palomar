module
public import QuantitativeFollowup.FollowupCavityGeneratedFutureOriginSourceReceiverProjections
public import QuantitativeFollowup.FollowupCavityGeneratedEndpointFutureProjection

@[expose] public section

/-! The active canonical future chart has the original full-record
future law. Clamped numerical indices disappear by actual strict-future
cell geometry; the padded root is removed by the genuine identity edge. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

theorem printedGeneratedFutureOriginChartRecordProject_law
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U) (j : Fin U.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : printedGeneratedOriginChartCell U γ h r)
    (hl : nativeStreamingGeneratedComponentClock U h (j.val+1) ≤ l ∧
      l ≤ nativeStreamingGeneratedComponentClock U h j)
    (hfuture : printedGeneratedOriginChartClock U γ h r < l) :
    (printedGeneratedComponentLaw D μ a (printedGeneratedOriginFutureChartComponent U γ j)
      (nativeStreamingGeneratedCrossEdgeAppend h (printedGeneratedOriginChartClock U γ h r) l)).map
        (printedGeneratedFutureOriginChartRecordProject U γ j) =
      (nativeStreamingOriginFutureProbability D μ a (nativeStreamingGeneratedComponentClock U h)
        U.tree (printedGeneratedFutureOriginChartOrigin U γ r) j l : Measure _) := by
  rcases γ with i | (i | u)
  · let v := printedGeneratedOriginChartFork U i
    have hv := printedGeneratedOriginChartFork_interior U i
    have hjv : j.val < v.depth := by
      by_contra hn
      have hq := nativeStreamingGeneratedComponentClock_antitone U h (show v.depth ≤ j.val by omega)
      exact (not_lt_of_ge (hl.2.trans hq)) hfuture
    let k := min j.val (v.depth-1)
    have hk : k = j.val := Nat.min_eq_left (by omega)
    have hkv : k < v.depth := by simpa only [hk] using hjv
    have hlk : nativeStreamingGeneratedComponentClock U h (k+1) ≤ l ∧
        l ≤ nativeStreamingGeneratedComponentClock U h k := by
      simpa only [hk] using hl
    have hx := printedGeneratedFutureVertexRecordProject_law D μ a U v hv.1 hv.2 k hkv h l hh hlk
    have he := congrArg (fun p => (nativeStreamingOriginFutureProbability D μ a
      (nativeStreamingGeneratedComponentClock U h) U.tree (.vertex v) p l).toMeasure) hk
    exact hx.trans he
  · let e := printedGeneratedOriginChartEdge U i
    have hje : j.val ≤ e.depth := by
      by_contra hn
      have hq := nativeStreamingGeneratedComponentClock_antitone U h (show e.depth+1 ≤ j.val by omega)
      exact (not_lt_of_ge (hl.2.trans (hq.trans hr.1))) hfuture
    let k := min j.val e.depth
    have hk : k = j.val := Nat.min_eq_left hje
    have hke : k ≤ e.depth := by simpa only [hk] using hje
    have hlk : nativeStreamingGeneratedComponentClock U h (k+1) ≤ l ∧
        l ≤ nativeStreamingGeneratedComponentClock U h k := by
      simpa only [hk] using hl
    have hx := nativeStreamingGeneratedSharedFutureEdgeComponent_record_law_append
      D μ a U e k hke h r l hh hr hlk hfuture
    have he := congrArg (fun p => (nativeStreamingOriginFutureProbability D μ a
      (nativeStreamingGeneratedComponentClock U h) U.tree (.edge e r) p l).toMeasure) hk
    unfold printedGeneratedComponentLaw
    rw [printedGeneratedComponentClock_eq_native]
    exact hx.trans he
  · let B := nativeStreamingGeneratedEndpointComponent U
    let v := nativeStreamingGeneratedEndpointVertex U (.root U.tree)
    have hv := nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)
    have hjv : j.val+1 < v.depth := by
      rw [nativeStreamingGeneratedEndpointVertex_depth]
      change j.val+1 < U.depth+1
      omega
    have hB : h ∈ nativeStreamingGeneratedComponentOrderSet B := by
      rwa [nativeStreamingGeneratedEndpointComponent_orderSet]
    have hlB : nativeStreamingGeneratedComponentClock B h (j.val+1+1) ≤ l ∧
        l ≤ nativeStreamingGeneratedComponentClock B h (j.val+1) := by
      simpa only [B,nativeStreamingGeneratedEndpointComponent_clock,
        nativeStreamingGeneratedEndpointClock_succ] using hl
    have hclock : nativeStreamingGeneratedComponentClock B h v.depth =
        nativeStreamingGeneratedComponentClock U h U.depth :=
      nativeStreamingGeneratedEndpointVertex_clock U h (.root U.tree)
    let C := printedGeneratedFutureVertexComponent B v hv.1 hv.2 (j.val+1) hjv
    let proj := printedGeneratedFutureVertexRecordProject (n:=n) B v hv.1 hv.2 (j.val+1) hjv
    let post : (PrintedGeneratedComponentRecord n B × (Configuration (n+1) × Configuration (n+1))) →
        PrintedGeneratedComponentRecord n U × (Configuration (n+1) × Configuration (n+1)) :=
      Prod.map (Prod.map id (nativeStreamingGeneratedEndpointRecordProject U)) id
    have hpost : Measurable post :=
      (measurable_id.prodMap (measurable_nativeStreamingGeneratedEndpointRecordProject U)).prodMap measurable_id
    have hproj : Measurable proj := measurable_printedGeneratedFutureVertexRecordProject _ _ _ _ _ _
    have hx := printedGeneratedFutureVertexRecordProject_law D μ a B v hv.1 hv.2 (j.val+1) hjv h l hB hlB
    have hx' : (printedGeneratedComponentLaw D μ a C
        (nativeStreamingGeneratedCrossEdgeAppend h (nativeStreamingGeneratedComponentClock U h U.depth) l)).map proj =
        (nativeStreamingOriginFutureProbability D μ a (nativeStreamingGeneratedComponentClock B h)
          B.tree (.vertex v) (j.val+1) l : Measure _) := by
      simpa only [hclock] using hx
    have hpad := nativeStreamingOriginFutureProbability_vertex_eq_law D μ a
      (nativeStreamingGeneratedComponentClock B h) (nativeStreamingGeneratedComponentClock_antitone B h)
      (nativeStreamingGeneratedComponentClock_terminal B h) B.tree v (j.val+1) hjv l hlB
    have hold := nativeStreamingOriginFutureProbability_vertex_eq_law D μ a
      (nativeStreamingGeneratedComponentClock U h) (nativeStreamingGeneratedComponentClock_antitone U h)
      (nativeStreamingGeneratedComponentClock_terminal U h) U.tree (.root U.tree) j.val j.isLt l hl
    change (printedGeneratedComponentLaw D μ a C
      (nativeStreamingGeneratedCrossEdgeAppend h (nativeStreamingGeneratedComponentClock U h U.depth) l)).map
        (post ∘ proj) = _
    rw [←Measure.map_map hpost hproj]
    exact (congrArg (fun Q : Measure (PrintedGeneratedComponentRecord n B ×
      (Configuration (n+1) × Configuration (n+1))) => Q.map post) (hx'.trans hpad)).trans
        ((nativeStreamingGeneratedEndpoint_future_law D μ a U h (.root U.tree) l).trans hold.symm)

end QuantitativeFollowup
