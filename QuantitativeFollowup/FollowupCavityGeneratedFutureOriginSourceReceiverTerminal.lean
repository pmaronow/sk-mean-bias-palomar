module
public import QuantitativeFollowup.FollowupCavityGeneratedFutureOriginSourceReceiverLaw
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternTerminalRepresentationFuture
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedEndpointVertexPatternsMoments

@[expose] public section

/-! The canonical future chart is a literal terminal-spin test on its
actual enlarged component, retaining every old spin and both fresh leaves. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n J : ℕ}

def printedGeneratedRefinedFutureTerminalProject {S : Type}
    (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex (observationRefineTree d T)) (p : ℕ) :
    TerminalSpins S (finiteCascadeFutureVertexGraft v p) → TerminalSpins S T × (S × S) :=
  fun σ =>
    let x := nativeStreamingPatternPairContinuationTerminalProjection (finiteCascadeFuturePairTree p) v σ
    (observationRefinementTerminalProject d T rfl x.1,x.2)

theorem printedGeneratedRefinedFutureTerminalProject_record {E S : Type}
    (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex (observationRefineTree d T)) (p : ℕ)
    (z : Records E S (finiteCascadeFutureVertexGraft v p)) :
    printedGeneratedRefinedFutureTerminalProject d T v p (finiteCascadeRecordTerminalSpins _ z) =
      (finiteCascadeRecordTerminalSpins T (observationRefinementProject d T
        (finiteCascadeFutureGraftExtract v p z).1),(finiteCascadeFutureGraftExtract v p z).2) := by
  unfold printedGeneratedRefinedFutureTerminalProject
  rw [nativeStreamingPatternPairContinuationTerminalProjection_record]
  dsimp only
  rw [observationRefinementTerminalProject_record]
  rfl

def printedGeneratedFutureVertexTerminalProject
    (U : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex U.tree)
    (hv0 : 0 < v.depth) (hvJ : v.depth < U.depth) (j : ℕ) (hj : j < v.depth) :
    CavityGeneratedComponentTerminal n (printedGeneratedFutureVertexComponent U v hv0 hvJ j hj) →
      CavityGeneratedComponentTerminal n U × (Configuration (n+1) × Configuration (n+1)) :=
  let B := printedGeneratedFutureVertexBase U v hv0 hvJ
  let e := printedGeneratedFutureCellEdge B j (hj.trans hvJ)
  printedGeneratedRefinedFutureTerminalProject (nativeStreamingEdgeSubdivision e.depth) B.tree
    (nativeStreamingGeneratedSharedFutureAnchor B v e) (e.depth+1)

theorem printedGeneratedFutureVertexTerminalProject_record
    (U : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex U.tree)
    (hv0 : 0 < v.depth) (hvJ : v.depth < U.depth) (j : ℕ) (hj : j < v.depth)
    (z : PrintedGeneratedComponentRecord n (printedGeneratedFutureVertexComponent U v hv0 hvJ j hj)) :
    printedGeneratedFutureVertexTerminalProject U v hv0 hvJ j hj
      (finiteCascadeRecordTerminalSpins _ z.2) =
      (finiteCascadeRecordTerminalSpins U.tree
        (printedGeneratedFutureVertexRecordProject U v hv0 hvJ j hj z).1.2,
        (printedGeneratedFutureVertexRecordProject U v hv0 hvJ j hj z).2) :=
  printedGeneratedRefinedFutureTerminalProject_record _ _ _ _ z.2

def printedGeneratedFutureEdgeTerminalProject
    (U : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge U.tree)
    (j : ℕ) (hj : j ≤ e.depth) :
    CavityGeneratedComponentTerminal n (nativeStreamingGeneratedSharedFutureEdgeComponent U e j hj) →
      CavityGeneratedComponentTerminal n U × (Configuration (n+1) × Configuration (n+1)) :=
  printedGeneratedRefinedFutureTerminalProject nativeStreamingPairObservationSubdivision U.tree
    (nativeStreamingGeneratedSharedFutureEdgeAnchor U e j hj)
    (nativeStreamingGeneratedSharedFutureEdgeSplit e.depth j)

theorem printedGeneratedFutureEdgeTerminalProject_record
    (U : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge U.tree)
    (j : ℕ) (hj : j ≤ e.depth)
    (z : PrintedGeneratedComponentRecord n (nativeStreamingGeneratedSharedFutureEdgeComponent U e j hj)) :
    printedGeneratedFutureEdgeTerminalProject U e j hj (finiteCascadeRecordTerminalSpins _ z.2) =
      (finiteCascadeRecordTerminalSpins U.tree
        (nativeStreamingGeneratedSharedFutureEdgeRecordProject U e j hj z).1.2,
        (nativeStreamingGeneratedSharedFutureEdgeRecordProject U e j hj z).2) :=
  printedGeneratedRefinedFutureTerminalProject_record _ _ _ _ z.2

def printedGeneratedFutureOriginChartTerminalProject
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U) (j : Fin U.depth) :
    CavityGeneratedComponentTerminal n (printedGeneratedOriginFutureChartComponent U γ j) →
      CavityGeneratedComponentTerminal n U × (Configuration (n+1) × Configuration (n+1)) :=
  match γ with
  | .inl i =>
      let v := printedGeneratedOriginChartFork U i
      let hv := printedGeneratedOriginChartFork_interior U i
      printedGeneratedFutureVertexTerminalProject U v hv.1 hv.2 (min j.val (v.depth-1))
        (Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hv.1 Nat.one_pos))
  | .inr (.inl i) => printedGeneratedFutureEdgeTerminalProject U (printedGeneratedOriginChartEdge U i)
      (min j.val (printedGeneratedOriginChartEdge U i).depth) (Nat.min_le_right _ _)
  | .inr (.inr _) => fun σ =>
      let B := nativeStreamingGeneratedEndpointComponent U
      let v := nativeStreamingGeneratedEndpointVertex U (.root U.tree)
      let hv := nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)
      let x := printedGeneratedFutureVertexTerminalProject B v hv.1 hv.2 (j.val+1)
        (by rw [nativeStreamingGeneratedEndpointVertex_depth]; change j.val+1 < U.depth+1; omega) σ
      (nativeStreamingGeneratedEndpointTerminalProject U x.1,x.2)

theorem printedGeneratedFutureOriginChartTerminalProject_record
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U) (j : Fin U.depth)
    (z : PrintedGeneratedComponentRecord n (printedGeneratedOriginFutureChartComponent U γ j)) :
    printedGeneratedFutureOriginChartTerminalProject U γ j (finiteCascadeRecordTerminalSpins _ z.2) =
      (finiteCascadeRecordTerminalSpins U.tree
        (printedGeneratedFutureOriginChartRecordProject U γ j z).1.2,
        (printedGeneratedFutureOriginChartRecordProject U γ j z).2) := by
  rcases γ with i | (i | u)
  · let v := printedGeneratedOriginChartFork U i
    have hv := printedGeneratedOriginChartFork_interior U i
    exact printedGeneratedFutureVertexTerminalProject_record U v hv.1 hv.2 _
      (Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hv.1 Nat.one_pos)) z
  · exact printedGeneratedFutureEdgeTerminalProject_record _ _ _ _ _
  · change (nativeStreamingGeneratedEndpointTerminalProject U
      (printedGeneratedFutureVertexTerminalProject
        (nativeStreamingGeneratedEndpointComponent U) (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
        (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
        (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2 (j.val+1) _
        (finiteCascadeRecordTerminalSpins _ z.2)).1,
      (printedGeneratedFutureVertexTerminalProject
        (nativeStreamingGeneratedEndpointComponent U) (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
        (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
        (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2 (j.val+1) _
        (finiteCascadeRecordTerminalSpins _ z.2)).2) = _
    rw [printedGeneratedFutureVertexTerminalProject_record,nativeStreamingGeneratedEndpointTerminalProject_record]
    rfl

theorem printedGeneratedFutureOriginChart_terminal_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U) (j : Fin U.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : printedGeneratedOriginChartCell U γ h r)
    (hl : nativeStreamingGeneratedComponentClock U h (j.val+1) ≤ l ∧
      l ≤ nativeStreamingGeneratedComponentClock U h j)
    (hfuture : printedGeneratedOriginChartClock U γ h r < l)
    (G : CavityGeneratedComponentTerminal n U × (Configuration (n+1) × Configuration (n+1)) → ℝ) :
    (∫ σ, G (printedGeneratedFutureOriginChartTerminalProject U γ j σ)
      ∂cavityGeneratedComponentTerminalMeasure D μ a (printedGeneratedOriginFutureChartComponent U γ j)
        (nativeStreamingGeneratedCrossEdgeAppend h (printedGeneratedOriginChartClock U γ h r) l)) =
      nativeStreamingTerminalMarkMoment
        (nativeStreamingOriginFutureProbability D μ a (nativeStreamingGeneratedComponentClock U h)
          U.tree (printedGeneratedFutureOriginChartOrigin U γ r) j l) G := by
  let V := printedGeneratedOriginFutureChartComponent U γ j
  let H := nativeStreamingGeneratedCrossEdgeAppend h (printedGeneratedOriginChartClock U γ h r) l
  let ψ : PrintedGeneratedComponentRecord n V → CavityGeneratedComponentTerminal n V :=
    fun z => finiteCascadeRecordTerminalSpins V.tree z.2
  have hψ : Measurable ψ := (measurable_finiteCascadeRecordTerminalSpins V.tree).comp measurable_snd
  have hmap := integral_map (μ:=printedGeneratedComponentLaw D μ a V H) hψ.aemeasurable
    (measurable_of_finite (fun σ => G (printedGeneratedFutureOriginChartTerminalProject U γ j σ))).aestronglyMeasurable
  let f : PrintedGeneratedComponentRecord n U × (Configuration (n+1) × Configuration (n+1)) → ℝ :=
    fun z => G (finiteCascadeRecordTerminalSpins U.tree z.1.2,z.2)
  have hf : Measurable f := (measurable_of_finite G).comp
    (((measurable_finiteCascadeRecordTerminalSpins U.tree).comp measurable_fst.snd).prodMk measurable_snd)
  have hp := printedGeneratedFutureOriginChartRecordProject_law D μ a U γ j h r l hh hr hl hfuture
  have hI := integral_map (μ:=printedGeneratedComponentLaw D μ a V H)
    (measurable_printedGeneratedFutureOriginChartRecordProject U γ j).aemeasurable hf.aestronglyMeasurable
  have hJ := congrArg (fun Q : Measure (PrintedGeneratedComponentRecord n U ×
    (Configuration (n+1) × Configuration (n+1))) => ∫ z,f z ∂Q) hp
  refine hmap.trans (Eq.trans ?_ (hI.symm.trans hJ))
  apply integral_congr_ae
  exact .of_forall fun z => congrArg G (printedGeneratedFutureOriginChartTerminalProject_record U γ j z)

theorem printedGeneratedFutureOriginChart_future_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U) (j : Fin U.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : printedGeneratedOriginChartCell U γ h r)
    (hl : nativeStreamingGeneratedComponentClock U h (j.val+1) ≤ l ∧
      l ≤ nativeStreamingGeneratedComponentClock U h j)
    (hfuture : printedGeneratedOriginChartClock U γ h r < l)
    (F : CavityGeneratedComponentTerminal n U → ℝ) :
    (∫ σ, nativeStreamingDefectSpinTest U.tree F l
      (printedGeneratedFutureOriginChartTerminalProject U γ j σ)
      ∂cavityGeneratedComponentTerminalMeasure D μ a (printedGeneratedOriginFutureChartComponent U γ j)
        (nativeStreamingGeneratedCrossEdgeAppend h (printedGeneratedOriginChartClock U γ h r) l)) =
      nativeStreamingPatternMoment D μ a (nativeStreamingGeneratedComponentClock U h)
        U.tree F (.future (printedGeneratedFutureOriginChartOrigin U γ r) j l) :=
  printedGeneratedFutureOriginChart_terminal_receiver D μ a U γ j h r l hh hr hl hfuture _

end QuantitativeFollowup
