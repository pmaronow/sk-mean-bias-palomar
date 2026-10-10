module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingMarkedContinuity

@[expose] public section

/-! The continuation attached to a native ancestral state may be any
finite genealogy. Its true conditional law and the entire old record are
identified with the literal enlarged genealogy. This covers independent
current marks and shared-future marks without a chosen-law premise. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ} {A : Type} [MeasurableSpace A]
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def nativeStreamingActualContinuationKernel (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap)
    (U : (j:ℕ)→FiniteTerminalGenealogy j)
    (extract : (j:ℕ)→Records (AnisotropicObservationState n) (Configuration n) (U j)→A)
    (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T) :
    Kernel (AnisotropicObservationState n×Records (AnisotropicObservationState n) (Configuration n) T) A :=
  ((anisotropicRecordedProfileTreeKernel D μ q (U v.depth)).map (extract v.depth)).comap
    (Function.uncurry (nativeStreamingVertexState v)) (nativeStreamingVertexState_measurable v)

theorem nativeStreamingActualContinuationKernel_markov (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap)
    (U : (j:ℕ)→FiniteTerminalGenealogy j)
    (extract : (j:ℕ)→Records (AnisotropicObservationState n) (Configuration n) (U j)→A)
    (he : ∀j,Measurable (extract j))
    (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T) :
    IsMarkovKernel (nativeStreamingActualContinuationKernel D μ q U extract T v) := by
  haveI := Kernel.IsMarkovKernel.map (anisotropicRecordedProfileTreeKernel D μ q (U v.depth))
    (he v.depth)
  unfold nativeStreamingActualContinuationKernel
  infer_instance

def nativeStreamingActualContinuationLaw (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (U : (j:ℕ)→FiniteTerminalGenealogy j)
    (extract : (j:ℕ)→Records (AnisotropicObservationState n) (Configuration n) (U j)→A)
    (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T) :=
  anisotropicRecordedProfileTreeLaw D μ a q T ⊗ₘ
    nativeStreamingActualContinuationKernel D μ q U extract T v

theorem nativeStreamingActualContinuationLaw_eq_graft (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (U : (j:ℕ)→FiniteTerminalGenealogy j)
    (extract : (j:ℕ)→Records (AnisotropicObservationState n) (Configuration n) (U j)→A)
    (he : ∀j,Measurable (extract j))
    (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T) :
    (anisotropicRecordedProfileTreeLaw D μ a q (finiteCascadeContinuationGraft U v)).map
      (fun z=>((z.1,(finiteCascadeContinuationExtract U extract v z.2).1),
        (finiteCascadeContinuationExtract U extract v z.2).2))=
      nativeStreamingActualContinuationLaw D μ a q U extract T v := by
  let κ:ℕ→Kernel (AnisotropicObservationState n) (AnisotropicObservationState n):=
    fun j=>anisotropicObservationTransition D μ (q (j+1)) (q j)
  let θ:Kernel (AnisotropicObservationState n) (Configuration n):=
    (anisotropicTerminalSpinKernel D).comap (anisotropicObservationParameter D)
      (measurable_anisotropicObservationParameter D)
  have hκ:∀j,IsMarkovKernel (κ j):=fun _=>inferInstance
  haveI:IsMarkovKernel θ:=inferInstance
  have hg:=nativeStreamingObservationGraft_joint_law κ hκ θ U extract he v
    (anisotropicObservationInitialLaw D μ a)
  unfold nativeStreamingContinuationMarkedLaw nativeStreamingContinuationVertexKernel
    nativeStreamingContinuationKernel at hg
  dsimp only [κ,θ] at hg
  simp_rw [←nativeStreamingRecordedProfileTreeKernel_eq_observation D μ q] at hg
  exact hg

def nativeStreamingActualContinuationProbability (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    (U : (j:ℕ)→FiniteTerminalGenealogy j)
    (extract : (j:ℕ)→Records (AnisotropicObservationState n) (Configuration n) (U j)→A)
    (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T) :
    ProbabilityMeasure ((AnisotropicObservationState n×
      Records (AnisotropicObservationState n) (Configuration n) T)×A) :=
  (anisotropicRecordedProfileProbability D μ a q (finiteCascadeContinuationGraft U v)).map
    (fun z=>((z.1,(finiteCascadeContinuationExtract U extract v z.2).1),
      (finiteCascadeContinuationExtract U extract v z.2).2))

theorem tendsto_nativeStreamingActualContinuationProbability
    [TopologicalSpace A] [BorelSpace A] [SecondCountableTopology A]
    {L : Type*} {l : Filter L} [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μj : L→Paper.ParisiMeasure} {μ : Paper.ParisiMeasure} (hμ : Tendsto μj l (𝓝 μ))
    (a : ℝ) (qj : L→ℕ→Paper.Overlap) (q : ℕ→Paper.Overlap)
    (U : (j:ℕ)→FiniteTerminalGenealogy j)
    (extract : (j:ℕ)→Records (AnisotropicObservationState n) (Configuration n) (U j)→A)
    (he : ∀j,Continuous (extract j))
    (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T)
    (hq : ∀p,p≤J→Tendsto (fun N=>qj N p) l (𝓝 (q p)))
    (hmono : ∀N,∀p,p<J→qj N (p+1)≤qj N p)
    (hMono : ∀p,p<J→q (p+1)≤q p) :
    Tendsto (fun N=>nativeStreamingActualContinuationProbability D (μj N) a (qj N) U extract T v) l
      (𝓝 (nativeStreamingActualContinuationProbability D μ a q U extract T v)) := by
  apply ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (tendsto_anisotropicRecordedProfileProbability_moving_schedule D hμ a qj q
      (finiteCascadeContinuationGraft U v) hq hmono hMono)
  have hc:=nativeStreamingContinuationExtract_continuous U extract he v
  exact (continuous_fst.prodMk (hc.fst.comp continuous_snd)).prodMk (hc.snd.comp continuous_snd)

end QuantitativeFollowup
