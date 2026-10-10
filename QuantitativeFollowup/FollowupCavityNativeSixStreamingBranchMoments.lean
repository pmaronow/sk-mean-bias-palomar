module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingTerminalMarkMoments
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingCurrentPairContinuity
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingCrossMarkedLaw

@[expose] public section

/-! The actual fixed-branch single, current-pair and cross-pair terms
converge with their literal atom and CDF coefficients.  Atom-preserving
rounding keeps these source coefficients exactly, including root atoms. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

theorem tendsto_nativeStreamingVertexSingleMoment
    {L : Type*} {l : Filter L} [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μj : L → Paper.ParisiMeasure} {μ : Paper.ParisiMeasure} (hμ : Tendsto μj l (𝓝 μ))
    (a : ℝ) (q : ℕ → Paper.Overlap) (hq : Antitone q)
    (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T)
    (G : TerminalSpins (Configuration n) T × Configuration n → ℝ) :
    Tendsto (fun N => nativeStreamingTerminalMarkMoment
      (nativeStreamingSingleVertexProbability D (μj N) a q T v) G) l
      (𝓝 (nativeStreamingTerminalMarkMoment (nativeStreamingSingleVertexProbability D μ a q T v) G)) :=
  tendsto_nativeStreamingTerminalMarkMoment
    (tendsto_nativeStreamingSingleVertexProbability D hμ a (fun _ => q) q T v
      (fun _ _ => tendsto_const_nhds) (fun _ p _ => hq (Nat.le_succ p))
      (fun p _ => hq (Nat.le_succ p))) G

theorem tendsto_nativeStreamingBranchSingleTerm (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (S : Finset Paper.Overlap) (hzero : zeroOverlap ∈ S)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex T) (hv : q v.depth∈S) (children : ℕ)
    (G : TerminalSpins (Configuration n) T × Configuration n → ℝ) :
    Tendsto (fun N => nativeStreamingBranchCharge (FRSB.preservingMeasure μ S N) a
      (q v.depth) children * nativeStreamingTerminalMarkMoment
        (nativeStreamingSingleVertexProbability D (FRSB.preservingMeasure μ S N) a q T v) G)
      atTop (𝓝 (nativeStreamingBranchCharge μ a (q v.depth) children *
        nativeStreamingTerminalMarkMoment (nativeStreamingSingleVertexProbability D μ a q T v) G)) := by
  simp_rw [nativeStreaming_branch_charge_preserved μ S hzero a ha hμ _ _ hv children]
  exact (tendsto_nativeStreamingVertexSingleMoment D (FRSB.tendsto_preservingMeasure μ S)
    a q hq T v G).const_mul _

theorem tendsto_nativeStreamingBranchCurrentTerm (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (S : Finset Paper.Overlap) (hzero : zeroOverlap ∈ S)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex T) (hv : q v.depth∈S) (children : ℕ)
    (G : TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ) :
    Tendsto (fun N => nativeStreamingBranchCharge (FRSB.preservingMeasure μ S N) a
      (q v.depth) children * Paper.parisiCDF (FRSB.preservingMeasure μ S N) (q v.depth) *
        nativeStreamingTerminalMarkMoment
          (nativeStreamingCurrentPairProbability D (FRSB.preservingMeasure μ S N) a q T v) G)
      atTop (𝓝 (nativeStreamingBranchCharge μ a (q v.depth) children * Paper.parisiCDF μ (q v.depth) *
        nativeStreamingTerminalMarkMoment (nativeStreamingCurrentPairProbability D μ a q T v) G)) := by
  simp_rw [nativeStreaming_branch_charge_preserved μ S hzero a ha hμ _ _ hv children,
    FRSB.preservingMeasure_cdf_mass μ S _ _ hv]
  exact (tendsto_nativeStreamingTerminalMarkMoment
    (tendsto_nativeStreamingCurrentPairProbability D (FRSB.tendsto_preservingMeasure μ S)
      a (fun _ => q) q T v (fun _ _ => tendsto_const_nhds)
      (fun _ p _ => hq (Nat.le_succ p)) (fun p _ => hq (Nat.le_succ p))) G).const_mul _

theorem tendsto_nativeStreamingBranchCrossTerm (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (S : Finset Paper.Overlap) (hzero : zeroOverlap ∈ S)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (v w : FiniteCascadeRecordVertex T) (hv : q v.depth∈S) (hw : q w.depth∈S)
    (childrenV childrenW : ℕ)
    (G : TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ) :
    Tendsto (fun N => nativeStreamingBranchCharge (FRSB.preservingMeasure μ S N) a
      (q v.depth) childrenV * nativeStreamingBranchCharge (FRSB.preservingMeasure μ S N) a
        (q w.depth) childrenW * nativeStreamingTerminalMarkMoment
          (nativeStreamingCrossVertexProbability D (FRSB.preservingMeasure μ S N) a q T v w) G)
      atTop (𝓝 (nativeStreamingBranchCharge μ a (q v.depth) childrenV *
        nativeStreamingBranchCharge μ a (q w.depth) childrenW *
          nativeStreamingTerminalMarkMoment (nativeStreamingCrossVertexProbability D μ a q T v w) G)) := by
  simp_rw [nativeStreaming_branch_charge_preserved μ S hzero a ha hμ _ _ hv childrenV,
    nativeStreaming_branch_charge_preserved μ S hzero a ha hμ _ _ hw childrenW]
  exact (tendsto_nativeStreamingTerminalMarkMoment
    (tendsto_nativeStreamingCrossVertexProbability D (FRSB.tendsto_preservingMeasure μ S)
      a (fun _ => q) q T v w (fun _ _ => tendsto_const_nhds)
      (fun _ p _ => hq (Nat.le_succ p)) (fun p _ => hq (Nat.le_succ p))) G).const_mul _

end QuantitativeFollowup
