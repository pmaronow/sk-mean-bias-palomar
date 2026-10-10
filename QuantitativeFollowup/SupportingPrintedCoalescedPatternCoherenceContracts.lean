module
public import QuantitativeFollowup.SupportingPrintedCoalescedPatternCoherenceLift
public import QuantitativeFollowup.SupportingPrintedCoalescedPatternCoherenceCross
public import QuantitativeFollowup.SupportingPrintedCoalescedPatternCoherenceIntegrability
public import QuantitativeFollowup.SupportingPrintedCoalescedPatternCoherenceFuture

@[expose] public section

/-! Actual first-six pattern callbacks satisfy the recursive coalesced
condition on every original tree, including nested zero-time components. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128

theorem nativeCoalescedOriginCoherent_originalFresh
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (i : ObservationLeaf T) :
    nativeCoalescedOriginCoherent μ a q T
      (fun o => nativeStreamingPatternMoment D μ a q T F (.originalFresh i o)) :=
  nativeCoalescedOriginCoherent_of_edges_root_coherent μ a q T _
    (nativeStreamingPatternMoment_originalFresh_vertex_root_coherent D μ a q T F i)
    (fun e he => (nativeStreamingPatternMoment_originalFresh_edge_same_time D μ a q hq hzero T F i e he).symm)
    (nativeStreamingPatternMoment_originalFresh_edge_upper D μ a q hq hzero T F i)
    (integrableOn_nativeStreamingCoalescedOriginalFresh D μ a q hq T F i)

theorem nativeCoalescedOriginCoherent_current
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ, |F σ|≤C) :
    nativeCoalescedOriginCoherent μ a q T (fun o => Paper.parisiCDF μ (nativeStreamingOriginLevel q o) *
      nativeStreamingPatternMoment D μ a q T F (.current o)) := by
  refine nativeCoalescedOriginCoherent_of_edges_root_coherent μ a q T _
    (nativeStreamingPatternMoment_current_vertex_root_coherent D μ a q T F)
    (fun e he => (nativeStreamingPatternMoment_current_edge_same_time D μ a q hq hzero T F e he).symm)
    ?_ (integrableOn_nativeStreamingCoalescedCurrent D μ a q hq T F C hC hF)
  intro e
  simp only [nativeStreamingOriginLevel,nativeStreamingEdgeChildVertex_depth]
  rw [nativeStreamingPatternMoment_current_edge_upper D μ a q hq hzero T F e]

theorem nativeCoalescedOriginCoherent_cross_left
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (o : NativeStreamingOrigin T) (ho : nativeCoalescedOriginValid q o) :
    nativeCoalescedOriginCoherent μ a q T
      (fun p => nativeStreamingPatternMoment D μ a q T F (.cross p o)) :=
  nativeCoalescedOriginCoherent_of_edges_root_coherent μ a q T _
    (nativeStreamingPatternMoment_cross_left_origin_root_coherent D μ a q T F o)
    (fun e he => (nativeStreamingPatternMoment_cross_valid_edge_same_time_left D μ a q hq hzero T F e he o ho).symm)
    (fun e => nativeStreamingPatternMoment_cross_valid_upper_left D μ a q hq hzero T F e o ho)
    (fun e => integrableOn_nativeStreamingCoalescedCross_left D μ a q hq T F e o ho)

theorem nativeCoalescedOriginCoherent_cross_right
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (o : NativeStreamingOrigin T) (ho : nativeCoalescedOriginValid q o) :
    nativeCoalescedOriginCoherent μ a q T
      (fun p => nativeStreamingPatternMoment D μ a q T F (.cross o p)) :=
  nativeCoalescedOriginCoherent_of_edges_root_coherent μ a q T _
    (nativeStreamingPatternMoment_cross_right_origin_root_coherent D μ a q T F o)
    (fun e he => (nativeStreamingPatternMoment_cross_valid_edge_same_time_right D μ a q hq hzero T F e he o ho).symm)
    (fun e => nativeStreamingPatternMoment_cross_valid_upper_right D μ a q hq hzero T F e o ho)
    (fun e => integrableOn_nativeStreamingCoalescedCross_right D μ a q hq T F e o ho)

theorem nativeCoalescedOriginCoherent_future
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ, |F σ|≤C) :
    nativeCoalescedOriginCoherent μ a q T
      (nativeStreamingPatternFutureIntegral D μ a q T F) :=
  nativeCoalescedOriginCoherent_of_edges_root_coherent μ a q T _
    (nativeStreamingPatternFutureIntegral_vertex_root_coherent D μ a q hq hzero T F)
    (fun e he => (nativeStreamingPatternFutureIntegral_edge_same_time D μ a q hq hzero T F e he).symm)
    (nativeStreamingPatternFutureIntegral_edge_child_endpoint D μ a q hq hzero T F)
    (integrableOn_nativeStreamingCoalescedFuture D μ a q hq T F C hC hF)

end QuantitativeFollowup
