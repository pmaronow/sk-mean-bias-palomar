module
public import QuantitativeFollowup.VectorQuantileBinPoint
public import FourPapersCommon.IntervalBoundaryStrips
public import HexagonPaper.MomentsArithmetic

@[expose] public section

/-! Actual superlevel sets inside a quantile bin lie in its two endpoint
strips.  The optimized strip width is 32ε/τ; no larger constant is substituted for the target. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper QuantitativeFollowup FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace HexagonPaper
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vector_quantile_bin_superlevel_volume_64 (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (I : Set ℝ) (hI : I.OrdConnected) (hDom : I⊆Ioc (0:ℝ) (1-s))
    (a d u τ : ℝ) (hd : 0≤d) (hu : 0<u) (hτ : 0<τ) (hdτ : d^2≤τ/4)
    (hRange : ∀w∈I,(parisiFreeQuantile μ s w:ℝ)∈Icc a (a+d))
    (hThreshold : ∀ᵐw ∂volume.restrict I,u≤Paper.parisiCDF μ (parisiFreeQuantile μ s w)) :
    volume.real {v | v∈I ∧ τ<vectorCenteredSelfOverlapSecond (n:=n) μ β t s ht.le (parisiFreeQuantile μ s v)}
      ≤64*(1/((n:ℝ)*((1-t)*β^2)*u))/τ := by
  let ε:=1/((n:ℝ)*((1-t)*β^2)*u)
  have hε : 0<ε:=by positivity
  have hδ : 0≤32*ε/τ:=by positivity
  have hb : BddBelow I:=⟨0,fun w hw=>(hDom hw).1.le⟩
  have ha : BddAbove I:=⟨1-s,fun w hw=>(hDom hw).2⟩
  have h:=volume_set_le_boundary_strips I
    {v | v∈I ∧ τ<vectorCenteredSelfOverlapSecond (n:=n) μ β t s ht.le (parisiFreeQuantile μ s v)}
    hb ha (32*ε/τ) hδ (fun v hv=>by
      refine ⟨hv.1,?_⟩
      by_cases hvi : v∈Ioo (sInf I) (sSup I)
      · have hp:=vector_quantile_bin_point_bound hn μ s β t hβ ht hs hμ hmin I hI hDom
          a d u hd hu hRange hThreshold hv.1 hvi
        have hex:=reciprocal_bin_exclusion_32 _ d ε τ (sSup I-v) (v-sInf I) hε hτ
          (sub_pos.mpr hvi.2) (sub_pos.mpr hvi.1) hdτ hv.2 hp
        exact hex.symm
      · have hl:=csInf_le hb hv.1
        have hr:=le_csSup ha hv.1
        change ¬(sInf I<v ∧ v<sSup I) at hvi
        by_cases hl' : sInf I<v
        · right
          have h:=not_lt.mp (fun hv'=>hvi ⟨hl',hv'⟩)
          linarith
        · left
          have h:=not_lt.mp hl'
          linarith)
  convert h using 1 <;> dsimp only [ε] <;> ring

end HexagonPaper
