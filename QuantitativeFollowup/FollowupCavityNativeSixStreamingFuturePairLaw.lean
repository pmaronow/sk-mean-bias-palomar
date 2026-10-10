module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingContinuationLaw
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingMarkedRefinement
public import FourPapersCommon.FiniteCascadeFutureVertexGraft

@[expose] public section

/-! A genuine shared future branch starts at the retained ancestral state,
runs to the selected future overlap, and then draws two independent
terminal spins. At every observed future point this is exactly the law
of the actual enlarged native genealogy. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreamingObservationPairSpins_continuous {E S:Type}
    [TopologicalSpace E] [TopologicalSpace S] {j:ℕ} (P:ObservationPairTree j) :
    Continuous (P.spins (E:=E) (S:=S)) := by
  induction P with
  | split j reverse =>
      cases reverse with
      | false =>
          exact ((nativeStreamingLinearSpin_continuous (E:=E) (S:=S) j).comp continuous_fst).prodMk
            ((nativeStreamingLinearSpin_continuous (E:=E) (S:=S) j).comp continuous_snd)
      | true =>
          exact ((nativeStreamingLinearSpin_continuous (E:=E) (S:=S) j).comp continuous_snd).prodMk
            ((nativeStreamingLinearSpin_continuous (E:=E) (S:=S) j).comp continuous_fst)
  | advance P ih => exact ih.comp continuous_snd

def nativeStreamingFuturePairKernel (D:AnisotropicSpinModel n)
    (μ:Paper.ParisiMeasure) (q:ℕ→Paper.Overlap) (T:FiniteTerminalGenealogy J)
    (v:FiniteCascadeRecordVertex T) (r:Paper.Overlap) :
    Kernel (AnisotropicObservationState n×Records (AnisotropicObservationState n) (Configuration n) T)
      (Configuration n×Configuration n) :=
  ((anisotropicObservationTerminalSpinKernel D μ r ×ₖ anisotropicObservationTerminalSpinKernel D μ r) ∘ₖ
    anisotropicObservationTransition D μ (q v.depth) r).comap
      (Function.uncurry (nativeStreamingVertexState v)) (nativeStreamingVertexState_measurable v)

instance nativeStreamingFuturePairKernel_markov (D:AnisotropicSpinModel n)
    (μ:Paper.ParisiMeasure) (q:ℕ→Paper.Overlap) (T:FiniteTerminalGenealogy J)
    (v:FiniteCascadeRecordVertex T) (r:Paper.Overlap) :
    IsMarkovKernel (nativeStreamingFuturePairKernel D μ q T v r) := by
  unfold nativeStreamingFuturePairKernel
  infer_instance

def nativeStreamingFuturePairLaw (D:AnisotropicSpinModel n)
    (μ:Paper.ParisiMeasure) (a:ℝ) (q:ℕ→Paper.Overlap) (T:FiniteTerminalGenealogy J)
    (v:FiniteCascadeRecordVertex T) (r:Paper.Overlap) :=
  anisotropicRecordedProfileTreeLaw D μ a q T ⊗ₘ nativeStreamingFuturePairKernel D μ q T v r

theorem nativeStreamingActualContinuationKernel_future_pair (D:AnisotropicSpinModel n)
    (μ:Paper.ParisiMeasure) (q:ℕ→Paper.Overlap) (hq:Antitone q)
    (hzero:q 0=1) (T:FiniteTerminalGenealogy J) (v:FiniteCascadeRecordVertex T)
    (p:ℕ) (hp:p≤v.depth) :
    nativeStreamingActualContinuationKernel D μ q
      (fun d=>(finiteCascadeFuturePairTree p d).tree)
      (fun d=>(finiteCascadeFuturePairTree p d).spins) T v=
      nativeStreamingFuturePairKernel D μ q T v (q p) := by
  unfold nativeStreamingActualContinuationKernel nativeStreamingFuturePairKernel
  rw [anisotropicRecordedPairSpinKernel D μ q hzero (finiteCascadeFuturePairTree p v.depth)
    (fun i _=>hq (Nat.le_succ i)),finiteCascadeFuturePairTree_split p v.depth hp]

theorem nativeStreamingFuturePairLaw_eq_graft (D:AnisotropicSpinModel n)
    (μ:Paper.ParisiMeasure) (a:ℝ) (q:ℕ→Paper.Overlap) (hq:Antitone q)
    (hzero:q 0=1) (T:FiniteTerminalGenealogy J) (v:FiniteCascadeRecordVertex T)
    (p:ℕ) (hp:p≤v.depth) :
    (anisotropicRecordedProfileTreeLaw D μ a q (finiteCascadeFutureVertexGraft v p)).map
      (fun z=>((z.1,(finiteCascadeFutureGraftExtract v p z.2).1),
        (finiteCascadeFutureGraftExtract v p z.2).2))=
      nativeStreamingFuturePairLaw D μ a q T v (q p) := by
  have hg:=nativeStreamingActualContinuationLaw_eq_graft D μ a q
    (fun d=>(finiteCascadeFuturePairTree p d).tree)
    (fun d=>(finiteCascadeFuturePairTree p d).spins)
    (fun d=>(finiteCascadeFuturePairTree p d).measurable_spins) T v
  unfold nativeStreamingActualContinuationLaw at hg
  rw [nativeStreamingActualContinuationKernel_future_pair D μ q hq hzero T v p hp] at hg
  exact hg

theorem nativeStreamingFuturePairKernel_refinement (D:AnisotropicSpinModel n)
    (μ:Paper.ParisiMeasure) (q Q:ℕ→Paper.Overlap) (d:ℕ→ℕ)
    (hlevels:∀j,Q (observationRefinementDepth d j)=q j)
    (T:FiniteTerminalGenealogy J) (v:FiniteCascadeRecordVertex T) (r:Paper.Overlap) :
    nativeStreamingFuturePairKernel D μ Q (observationRefineTree d T)
      (nativeStreamingRefinementVertexEmbed d T v) r=
      (nativeStreamingFuturePairKernel D μ q T v r).comap
        (Prod.map id (observationRefinementProject d T))
        (measurable_id.prodMap (measurable_observationRefinementProject d T)) := by
  ext z σ hs
  change (((anisotropicObservationTerminalSpinKernel D μ r ×ₖ
    anisotropicObservationTerminalSpinKernel D μ r) ∘ₖ anisotropicObservationTransition D μ
      (Q (nativeStreamingRefinementVertexEmbed d T v).depth) r)
        (nativeStreamingVertexState (nativeStreamingRefinementVertexEmbed d T v) z.1 z.2)) σ=
    (((anisotropicObservationTerminalSpinKernel D μ r ×ₖ
      anisotropicObservationTerminalSpinKernel D μ r) ∘ₖ anisotropicObservationTransition D μ
        (q v.depth) r) (nativeStreamingVertexState v z.1 (observationRefinementProject d T z.2))) σ
  rw [nativeStreamingRefinementVertexEmbed_depth,hlevels,nativeStreamingRefinementVertexEmbed_state]

end QuantitativeFollowup
