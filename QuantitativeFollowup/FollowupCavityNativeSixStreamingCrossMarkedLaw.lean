module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingCrossGraft
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingMarkedContinuity

@[expose] public section

/-! The actual independent fresh-spin product at arbitrary retained
vertices is the pushforward of the full enlarged native genealogy.  Its
complete old-record marginal and weak-profile continuity follow from
that genuine model identification. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J:ℕ}
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreamingCrossSpinExtract_continuous {E S:Type}
    [MeasurableSpace E] [MeasurableSpace S]
    [TopologicalSpace E] [TopologicalSpace S]
    {j:ℕ} {T:FiniteTerminalGenealogy j} (v w:FiniteCascadeRecordVertex T) :
    Continuous (finiteCascadeCrossContinuationExtract (E:=E) (S:=S)
      observationLinearTree observationLinearSpin v w) := by
  have h1:=nativeStreamingContinuationExtract_continuous (E:=E) (S:=S)
    observationLinearTree observationLinearSpin
    nativeStreamingLinearSpin_continuous (finiteCascadeContinuationVertexEmbed observationLinearTree v w)
  have h2:=(nativeStreamingContinuationExtract_continuous (E:=E) (S:=S)
    observationLinearTree observationLinearSpin
    nativeStreamingLinearSpin_continuous v).comp h1.fst
  exact h2.fst.prodMk (h2.snd.prodMk h1.snd)

def nativeStreamingCrossVertexKernel (D:AnisotropicSpinModel n)
    (μ:Paper.ParisiMeasure) (q:ℕ→Paper.Overlap) (T:FiniteTerminalGenealogy J)
    (v w:FiniteCascadeRecordVertex T) :=
  nativeStreamingSingleVertexKernel D μ q T v ×ₖ nativeStreamingSingleVertexKernel D μ q T w

instance nativeStreamingCrossVertexKernel_markov (D:AnisotropicSpinModel n)
    (μ:Paper.ParisiMeasure) (q:ℕ→Paper.Overlap) (T:FiniteTerminalGenealogy J)
    (v w:FiniteCascadeRecordVertex T) :
    IsMarkovKernel (nativeStreamingCrossVertexKernel D μ q T v w) := by
  unfold nativeStreamingCrossVertexKernel
  infer_instance

def nativeStreamingCrossVertexLaw (D:AnisotropicSpinModel n)
    (μ:Paper.ParisiMeasure) (a:ℝ) (q:ℕ→Paper.Overlap) (T:FiniteTerminalGenealogy J)
    (v w:FiniteCascadeRecordVertex T) :=
  anisotropicRecordedProfileTreeLaw D μ a q T ⊗ₘ nativeStreamingCrossVertexKernel D μ q T v w

theorem nativeStreamingCrossVertexLaw_eq_graft (D:AnisotropicSpinModel n)
    (μ:Paper.ParisiMeasure) (a:ℝ) (q:ℕ→Paper.Overlap) (hq:Antitone q)
    (hzero:q 0=1) (T:FiniteTerminalGenealogy J) (v w:FiniteCascadeRecordVertex T) :
    (anisotropicRecordedProfileTreeLaw D μ a q
      (finiteCascadeCrossContinuationGraft observationLinearTree v w)).map
      (fun z=>((z.1,(finiteCascadeCrossContinuationExtract observationLinearTree
        observationLinearSpin v w z.2).1),
        (finiteCascadeCrossContinuationExtract observationLinearTree observationLinearSpin v w z.2).2))=
      nativeStreamingCrossVertexLaw D μ a q T v w := by
  let κ:ℕ→Kernel (AnisotropicObservationState n) (AnisotropicObservationState n):=
    fun j=>anisotropicObservationTransition D μ (q (j+1)) (q j)
  let θ:Kernel (AnisotropicObservationState n) (Configuration n):=
    (anisotropicTerminalSpinKernel D).comap (anisotropicObservationParameter D)
      (measurable_anisotropicObservationParameter D)
  have hκ:∀j,IsMarkovKernel (κ j):=fun _=>inferInstance
  haveI:IsMarkovKernel θ:=inferInstance
  have hg:=nativeStreamingCrossObservationGraft_joint_law κ hκ θ observationLinearTree
    observationLinearSpin (fun j=>measurable_observationLinearSpin j) v w
    (anisotropicObservationInitialLaw D μ a)
  unfold nativeStreamingCrossContinuationMarkedLaw nativeStreamingCrossContinuationKernel
    nativeStreamingContinuationVertexKernel nativeStreamingContinuationKernel at hg
  dsimp only [κ,θ] at hg
  simp_rw [←nativeStreamingRecordedProfileTreeKernel_eq_observation D μ q] at hg
  have hv:=anisotropicRecordedLinearSpinKernel D μ q hzero v.depth (fun i _=>hq (Nat.le_succ i))
  have hw:=anisotropicRecordedLinearSpinKernel D μ q hzero w.depth (fun i _=>hq (Nat.le_succ i))
  rw [hv,hw] at hg
  exact hg

def nativeStreamingCrossVertexProbability (D:AnisotropicSpinModel n)
    (μ:Paper.ParisiMeasure) (a:ℝ) (q:ℕ→Paper.Overlap) (T:FiniteTerminalGenealogy J)
    (v w:FiniteCascadeRecordVertex T) :
    ProbabilityMeasure ((AnisotropicObservationState n×
      Records (AnisotropicObservationState n) (Configuration n) T)×(Configuration n×Configuration n)) :=
  (anisotropicRecordedProfileProbability D μ a q
    (finiteCascadeCrossContinuationGraft observationLinearTree v w)).map
      (fun z=>((z.1,(finiteCascadeCrossContinuationExtract observationLinearTree
        observationLinearSpin v w z.2).1),
        (finiteCascadeCrossContinuationExtract observationLinearTree observationLinearSpin v w z.2).2))

theorem nativeStreamingCrossVertexProbability_eq_law (D:AnisotropicSpinModel n)
    (μ:Paper.ParisiMeasure) (a:ℝ) (q:ℕ→Paper.Overlap) (hq:Antitone q)
    (hzero:q 0=1) (T:FiniteTerminalGenealogy J) (v w:FiniteCascadeRecordVertex T) :
    (nativeStreamingCrossVertexProbability D μ a q T v w:Measure _)=
      nativeStreamingCrossVertexLaw D μ a q T v w := by
  change (anisotropicRecordedProfileTreeLaw D μ a q _).map _=_
  exact nativeStreamingCrossVertexLaw_eq_graft D μ a q hq hzero T v w

theorem tendsto_nativeStreamingCrossVertexProbability
    {L:Type*} {l:Filter L} [l.IsCountablyGenerated] (D:AnisotropicSpinModel n)
    {μj:L→Paper.ParisiMeasure} {μ:Paper.ParisiMeasure} (hμ:Tendsto μj l (𝓝 μ))
    (a:ℝ) (qj:L→ℕ→Paper.Overlap) (q:ℕ→Paper.Overlap)
    (T:FiniteTerminalGenealogy J) (v w:FiniteCascadeRecordVertex T)
    (hq:∀p,p≤J→Tendsto (fun N=>qj N p) l (𝓝 (q p)))
    (hmono:∀N,∀p,p<J→qj N (p+1)≤qj N p)
    (hMono:∀p,p<J→q (p+1)≤q p) :
    Tendsto (fun N=>nativeStreamingCrossVertexProbability D (μj N) a (qj N) T v w) l
      (𝓝 (nativeStreamingCrossVertexProbability D μ a q T v w)) := by
  haveI : BorelSpace (Records (AnisotropicObservationState n) (Configuration n) T) :=
    anisotropicObservationRecords_borel T
  haveI : SecondCountableTopology (Records (AnisotropicObservationState n) (Configuration n) T) :=
    inferInstance
  apply ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (tendsto_anisotropicRecordedProfileProbability_moving_schedule D hμ a qj q
      (finiteCascadeCrossContinuationGraft observationLinearTree v w) hq hmono hMono)
  have hc:=nativeStreamingCrossSpinExtract_continuous (E:=AnisotropicObservationState n)
    (S:=Configuration n) v w
  exact (continuous_fst.prodMk (hc.fst.comp continuous_snd)).prodMk (hc.snd.comp continuous_snd)

end QuantitativeFollowup
