module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeSelectedGeometryClock
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPreservingIntegrals

@[expose] public section

/-! The actual selected common-path clock is continuous in both marks.
Its true right CDF also converges under the atom-preserving quantizer,
including shared-edge diagonal atoms and repeated physical times. -/
noncomputable section
open Set Filter
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option maxHeartbeats 900000

theorem continuous_nativeStreamingSelectedCommonClock (c de df : ℕ) (qc : Paper.Overlap) :
    Continuous (fun z : Paper.Overlap×Paper.Overlap=>
      nativeStreamingSelectedCommonClock c de df z.1 z.2 qc) := by
  classical
  unfold nativeStreamingSelectedCommonClock
  split_ifs
  · exact continuous_fst.min continuous_snd
  · exact continuous_fst
  · exact continuous_snd
  · exact continuous_const

theorem tendsto_nativeStreamingSelectedCommonClock_preserving (S : Finset Paper.Overlap)
    (c de df : ℕ) (r l qc : Paper.Overlap) :
    Tendsto (fun N=>nativeStreamingSelectedCommonClock c de df
      (FRSB.preservingRound S N r) (FRSB.preservingRound S N l) qc) atTop
        (𝓝 (nativeStreamingSelectedCommonClock c de df r l qc)) :=
  ((continuous_nativeStreamingSelectedCommonClock c de df qc).tendsto (r,l)).comp
    ((FRSB.tendsto_preservingRound S r).prodMk_nhds (FRSB.tendsto_preservingRound S l))

theorem nativeStreamingSelectedCommonClock_preservingRound (S : Finset Paper.Overlap)
    (c de df : ℕ) (r l qc : Paper.Overlap) (hqc : qc∈S) :
    ∀ᶠN in atTop,nativeStreamingSelectedCommonClock c de df
      (FRSB.preservingRound S N r) (FRSB.preservingRound S N l) qc=
        FRSB.preservingRound S N (nativeStreamingSelectedCommonClock c de df r l qc) := by
  classical
  unfold nativeStreamingSelectedCommonClock
  split_ifs
  · filter_upwards [nativeStreaming_round_le_eventually S r l] with N hN
    by_cases hrl : r≤l
    · rw [min_eq_left hrl,min_eq_left (hN.mpr hrl)]
    · rw [min_eq_right (le_of_not_ge hrl),min_eq_right (le_of_not_ge (mt hN.mp hrl))]
  · exact .of_forall fun _=>rfl
  · exact .of_forall fun _=>rfl
  · exact .of_forall fun N=>(FRSB.preservingRound_fixed S N qc hqc).symm

theorem tendsto_nativeStreamingSelectedCommonClock_CDF_preserving (μ : Paper.ParisiMeasure)
    (S : Finset Paper.Overlap) (c de df : ℕ) (r l qc : Paper.Overlap) (hqc : qc∈S) :
    Tendsto (fun N=>Paper.parisiCDF (FRSB.preservingMeasure μ S N)
      (nativeStreamingSelectedCommonClock c de df
        (FRSB.preservingRound S N r) (FRSB.preservingRound S N l) qc : Paper.Overlap)) atTop
        (𝓝 (Paper.parisiCDF μ (nativeStreamingSelectedCommonClock c de df r l qc : Paper.Overlap))) := by
  apply Tendsto.congr' _
    (nativeStreaming_preserving_cdf_at_round_tendsto μ S
      (nativeStreamingSelectedCommonClock c de df r l qc))
  filter_upwards [nativeStreamingSelectedCommonClock_preservingRound S c de df r l qc hqc]
    with N hN
  rw [hN]

end QuantitativeFollowup
