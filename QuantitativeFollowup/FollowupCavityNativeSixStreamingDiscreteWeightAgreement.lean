module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingCharges
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOriginWeightIntegral
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeSelectedGeometry

@[expose] public section

/-! The exact incoming-mass algebra needed to compare a finite charge
sum with the Stieltjes origin expression. Scheme masses are the CDF at
the next lower clock, rather than at the vertex clock. The edge-atom
identity and fork coherence are explicit structural inputs here; their
actual marked-law instances are separate probability statements. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

theorem nativeStreamingVertexChargeSum_change_incoming (b : ℕ → ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (s t : ℝ)
    (φ : FiniteCascadeRecordVertex T → ℝ) :
    nativeStreamingVertexChargeSum b s T φ =
      nativeStreamingVertexChargeSum b t T φ + (t-s)*φ (.root T) := by
  simp only [nativeStreamingVertexChargeSum, finiteCascadeVertexCharges,
    List.map_cons, List.sum_cons]
  ring

theorem nativeStreamingVertexChargeSum_advance (b : ℕ → ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (s : ℝ)
    (φ : FiniteCascadeRecordVertex T.advance → ℝ) :
    nativeStreamingVertexChargeSum b s T.advance φ =
      nativeStreamingVertexChargeSum b (b j) T (fun v => φ (.child v)) +
        (b j-s)*φ (.root T.advance) := by
  simp only [nativeStreamingVertexChargeSum, finiteCascadeVertexCharges,
    finiteCascadeVertexInteriorCharges, finiteCascadeTreeRootCoefficient,
    List.map_cons, List.sum_cons, List.map_map, Function.comp_def]
  ring

theorem nativeStreamingVertexChargeSum_fork (b : ℕ → ℝ)
    {j : ℕ} (T U : FiniteTerminalGenealogy j) (s : ℝ)
    (φ : FiniteCascadeRecordVertex (.fork T U) → ℝ)
    (hleft : φ (.left (.root T)) = φ (.root (.fork T U)))
    (hright : φ (.right (.root U)) = φ (.root (.fork T U))) :
    nativeStreamingVertexChargeSum b s (.fork T U) φ =
      nativeStreamingVertexChargeSum b (b j) T (fun v => φ (.left v)) +
      nativeStreamingVertexChargeSum b (b j) U (fun v => φ (.right v)) +
        (2*b j-s)*φ (.root (.fork T U)) := by
  simp only [nativeStreamingVertexChargeSum, finiteCascadeVertexCharges,
    finiteCascadeVertexInteriorCharges, finiteCascadeTreeRootCoefficient,
    List.map_cons, List.sum_cons, List.map_append, List.sum_append,
    List.map_map, Function.comp_def, hleft, hright]
  ring

theorem nativeStreamingVertexChargeSum_eq_originWeightIntegral_discrete
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap) (b : ℕ → ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (s : ℝ)
    (Φ : NativeStreamingOrigin T → ℝ)
    (hb : ∀i<j, b i = Paper.parisiCDF μ (q (i+1)))
    (hΦ : nativeStreamingRootCoherent T (fun v => Φ (.vertex v)))
    (hedge : ∀e : NativeStreamingEdge T,
      (∫r in Ioc (q (e.depth+1)) (q e.depth), Φ (.edge e r)
        ∂parisiFreeMeasure μ a) =
      (Paper.parisiCDF μ (q e.depth)-b e.depth) *
        Φ (.vertex (nativeStreamingEdgeChildVertex e))) :
    nativeStreamingVertexChargeSum b s T (fun v => Φ (.vertex v)) =
      nativeStreamingOriginWeightIntegral μ a q T s Φ := by
  induction T generalizing s with
  | leaf =>
      simp only [nativeStreamingVertexChargeSum, finiteCascadeVertexCharges,
        finiteCascadeVertexInteriorCharges, finiteCascadeTreeRootCoefficient,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        nativeStreamingOriginWeightIntegral]
  | @advance j T ih =>
      have hbT : ∀i<j, b i = Paper.parisiCDF μ (q (i+1)) :=
        fun i hi => hb i (hi.trans (Nat.lt_succ_self j))
      have heT : ∀e : NativeStreamingEdge T,
          (∫r in Ioc (q (e.depth+1)) (q e.depth),
            Φ (nativeStreamingOriginChild (.edge e r)) ∂parisiFreeMeasure μ a) =
          (Paper.parisiCDF μ (q e.depth)-b e.depth) *
            Φ (nativeStreamingOriginChild (.vertex (nativeStreamingEdgeChildVertex e))) := by
        intro e
        exact hedge (.child e)
      rw [nativeStreamingVertexChargeSum_advance,
        nativeStreamingVertexChargeSum_change_incoming b T (b j)
          (Paper.parisiCDF μ (q j))]
      rw [ih (Paper.parisiCDF μ (q j))
        (fun o => Φ (nativeStreamingOriginChild o)) hbT hΦ heT]
      change _ = nativeStreamingOriginWeightIntegral μ a q T
        (Paper.parisiCDF μ (q j)) (fun o => Φ (nativeStreamingOriginChild o)) +
        (∫r in Ioc (q (j+1)) (q j), Φ (.edge (.here T) r) ∂parisiFreeMeasure μ a) +
        (Paper.parisiCDF μ (q (j+1))-s)*Φ (.vertex (.root T.advance))
      rw [hedge (.here T), hb j (Nat.lt_succ_self j)]
  | @fork j T U ihT ihU =>
      obtain ⟨hleft,hright,hT,hU⟩ := hΦ
      have heT : ∀e : NativeStreamingEdge T,
          (∫r in Ioc (q (e.depth+1)) (q e.depth),
            Φ (nativeStreamingOriginLeft (.edge e r)) ∂parisiFreeMeasure μ a) =
          (Paper.parisiCDF μ (q e.depth)-b e.depth) *
            Φ (nativeStreamingOriginLeft (.vertex (nativeStreamingEdgeChildVertex e))) := by
        intro e
        exact hedge (.left e)
      have heU : ∀e : NativeStreamingEdge U,
          (∫r in Ioc (q (e.depth+1)) (q e.depth),
            Φ (nativeStreamingOriginRight (.edge e r)) ∂parisiFreeMeasure μ a) =
          (Paper.parisiCDF μ (q e.depth)-b e.depth) *
            Φ (nativeStreamingOriginRight (.vertex (nativeStreamingEdgeChildVertex e))) := by
        intro e
        exact hedge (.right e)
      rw [nativeStreamingVertexChargeSum_fork b T U s _ hleft hright,
        nativeStreamingVertexChargeSum_change_incoming b T (b j)
          (Paper.parisiCDF μ (q j)),
        nativeStreamingVertexChargeSum_change_incoming b U (b j)
          (Paper.parisiCDF μ (q j))]
      rw [ihT (Paper.parisiCDF μ (q j))
        (fun o => Φ (nativeStreamingOriginLeft o)) hb hT heT,
        ihU (Paper.parisiCDF μ (q j))
        (fun o => Φ (nativeStreamingOriginRight o)) hb hU heU]
      simp only [nativeStreamingOriginWeightIntegral, nativeStreamingOriginLeft,
        nativeStreamingOriginRight, hleft, hright]
      ring

end QuantitativeFollowup
