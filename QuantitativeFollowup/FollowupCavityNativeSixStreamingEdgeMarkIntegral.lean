module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingTerminalMarkMoments
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPreservingIntegrals

@[expose] public section

/-! Genuine variable-edge fresh-spin integrals converge under the
atom-preserving approximation.  The test, bound, measurability and moving
marked-law convergence are supplied by the actual finite terminal-spin
space and native genealogy, rather than by an assumed integral limit. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n J:ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

def nativeStreamingEdgeMaskedMoment (D:AnisotropicSpinModel n)
    (μ:Paper.ParisiMeasure) (a:ℝ) (q:ℕ→Paper.Overlap)
    (T:FiniteTerminalGenealogy J) (e:NativeStreamingEdge T)
    (S:Finset Paper.Overlap) (G:TerminalSpins (Configuration n) T×Configuration n→ℝ)
    (r:Paper.Overlap) : ℝ :=
  if q (e.depth+1)<r ∧ r<q e.depth ∧ r∉S then
    nativeStreamingTerminalMarkMoment (nativeStreamingEdgeSingleMarkProbability D μ a q T e r) G
  else 0

theorem measurable_nativeStreamingEdgeMaskedMoment (D:AnisotropicSpinModel n)
    (μ:Paper.ParisiMeasure) (a:ℝ) (q:ℕ→Paper.Overlap) (hq:Antitone q)
    (T:FiniteTerminalGenealogy J) (e:NativeStreamingEdge T)
    (S:Finset Paper.Overlap) (G:TerminalSpins (Configuration n) T×Configuration n→ℝ) :
    Measurable (nativeStreamingEdgeMaskedMoment D μ a q T e S G) := by
  classical
  have hc:ContinuousOn (fun r=>nativeStreamingTerminalMarkMoment
      (nativeStreamingEdgeSingleMarkProbability D μ a q T e r) G)
      (Icc (q (e.depth+1)) (q e.depth)) :=
    continuousOn_iff_continuous_restrict.mpr
      (continuous_nativeStreamingEdgeTerminalMarkMoment D μ a q hq T e G)
  have hs:MeasurableSet {r:Paper.Overlap | q (e.depth+1)<r ∧ r<q e.depth ∧ r∉S}:=
    isOpen_Ioi.measurableSet.inter (isOpen_Iio.measurableSet.inter S.finite_toSet.measurableSet.compl)
  convert (hc.mono (fun r hr=>⟨hr.1.le,hr.2.1.le⟩)).measurable_piecewise
    (g:=fun _=> (0:ℝ)) continuousOn_const hs using 1
  funext r
  by_cases hr:q (e.depth+1)<r ∧ r<q e.depth ∧ r∉S <;>
    simp [nativeStreamingEdgeMaskedMoment,Set.piecewise,hr]

theorem nativeStreamingEdgeMaskedMoment_abs_le (D:AnisotropicSpinModel n)
    (μ:Paper.ParisiMeasure) (a:ℝ) (q:ℕ→Paper.Overlap)
    (T:FiniteTerminalGenealogy J) (e:NativeStreamingEdge T)
    (S:Finset Paper.Overlap) (G:TerminalSpins (Configuration n) T×Configuration n→ℝ)
    (r:Paper.Overlap) :
    |nativeStreamingEdgeMaskedMoment D μ a q T e S G r|≤nativeStreamingTerminalMarkBound T G := by
  classical
  unfold nativeStreamingEdgeMaskedMoment
  split_ifs
  · exact nativeStreamingTerminalMarkMoment_abs_le _ G
  · simpa only [abs_zero] using nativeStreamingTerminalMarkBound_nonneg T G

theorem nativeStreamingEdgeMaskedMoment_preserving_tendsto (D:AnisotropicSpinModel n)
    (μ:Paper.ParisiMeasure) (a:ℝ) (q:ℕ→Paper.Overlap) (hq:Antitone q)
    (T:FiniteTerminalGenealogy J) (e:NativeStreamingEdge T)
    (S:Finset Paper.Overlap) (hlo:q (e.depth+1)∈S) (hhi:q e.depth∈S)
    (G:TerminalSpins (Configuration n) T×Configuration n→ℝ) (r:Paper.Overlap) :
    Tendsto (fun N=>nativeStreamingEdgeMaskedMoment D (FRSB.preservingMeasure μ S N) a q T e S G
      (FRSB.preservingRound S N r)) atTop
      (𝓝 (nativeStreamingEdgeMaskedMoment D μ a q T e S G r)) := by
  classical
  have hm (N:ℕ):
      (q (e.depth+1)<FRSB.preservingRound S N r ∧
        FRSB.preservingRound S N r<q e.depth ∧ FRSB.preservingRound S N r∉S) ↔
      (q (e.depth+1)<r ∧ r<q e.depth ∧ r∉S) := by
    simp only [FRSB.preservingRound_gt_iff S N r _ hlo,
      FRSB.preservingRound_lt_iff S N r _ hhi,nativeStreaming_round_mem_prescribed_iff]
  by_cases hr:q (e.depth+1)<r ∧ r<q e.depth ∧ r∉S
  · have hb (N:ℕ):q (e.depth+1)≤FRSB.preservingRound S N r ∧
        FRSB.preservingRound S N r≤q e.depth:=
      ⟨((hm N).mpr hr).1.le,((hm N).mpr hr).2.1.le⟩
    simpa [nativeStreamingEdgeMaskedMoment,hm,hr] using
      tendsto_nativeStreamingEdgeTerminalMarkMoment D (FRSB.tendsto_preservingMeasure μ S)
        a q hq T e (FRSB.tendsto_preservingRound S r) hb ⟨hr.1.le,hr.2.1.le⟩ G
  · simpa [nativeStreamingEdgeMaskedMoment,hm,hr] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

theorem tendsto_nativeStreamingEdgeMarkedFreeIntegral (D:AnisotropicSpinModel n)
    (μ:Paper.ParisiMeasure) (a:ℝ) (ha:a∈Icc (0:ℝ) 1) (hμ:μ∈scalarFloor a)
    (q:ℕ→Paper.Overlap) (hq:Antitone q) (T:FiniteTerminalGenealogy J) (e:NativeStreamingEdge T)
    (S:Finset Paper.Overlap) (hzero:zeroOverlap∈S)
    (hlo:q (e.depth+1)∈S) (hhi:q e.depth∈S)
    (G:TerminalSpins (Configuration n) T×Configuration n→ℝ) :
    Tendsto (fun N=>∫r,nativeStreamingEdgeMaskedMoment D (FRSB.preservingMeasure μ S N) a q T e S G r
      ∂parisiFreeMeasure (FRSB.preservingMeasure μ S N) a) atTop
      (𝓝 (∫r,nativeStreamingEdgeMaskedMoment D μ a q T e S G r ∂parisiFreeMeasure μ a)) :=
  nativeStreaming_free_integral_tendsto μ S hzero a ha hμ _ _
    (fun N=>measurable_nativeStreamingEdgeMaskedMoment D _ a q hq T e S G)
    (nativeStreamingTerminalMarkBound T G) (nativeStreamingTerminalMarkBound_nonneg T G)
    (fun N r=>nativeStreamingEdgeMaskedMoment_abs_le D _ a q T e S G r)
    (nativeStreamingEdgeMaskedMoment_preserving_tendsto D μ a q hq T e S hlo hhi G)

end QuantitativeFollowup
