module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingFiniteTreeAgreement
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingMarkedLaw
public import QuantitativeFollowup.AnisotropicObservationSchemeEmbedding
public import FourPapersCommon.FiniteCascadeVertexGraftLaw

@[expose] public section

/-! Exact finite/native conditional terminal-spin kernel agreement at
every retained scheme depth, for every original disorder and field. The
identity follows from complete recorded-kernel energy transport, rather
than a supplied conditional-spin-law assumption. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreamingObservationLinearSpin_treeMap {E F S : Type}
    (φ : E → F) (j : ℕ) (z : Records E S (observationLinearTree j)) :
    observationLinearSpin j (observationTreeMap φ (observationLinearTree j) z) =
      observationLinearSpin j z := by
  induction j with
  | zero => rfl
  | succ j ih => exact ih z.2

theorem nativeStreamingFiniteObservationLinearKernel_spin
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (j : ℕ) :
    (finiteCascadeTreeRecordKernel (fun _ : Configuration n => 0)
      (anisotropicSchemeMass s)
      (fun l => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l))
      (observationLinearTree j)).map (observationLinearSpin j) =
      finiteStateCascadeGibbsKernel (fun _ : Configuration n => 0)
        (anisotropicSchemeMass s)
        (fun l => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) j := by
  induction j with
  | zero =>
      simp only [observationLinearTree, finiteCascadeTreeRecordKernel,
        observationLinearSpin, Kernel.map_id, finiteStateCascadeGibbsKernel,
        finiteStateCascadeFieldKernel, OverlapPaper.sourceKernelLaw, Kernel.comp_id]
  | succ j ih =>
      haveI := isMarkovKernel_finiteCascadeTreeRecordKernel (fun _ : Configuration n => 0)
        (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
        (fun l => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l))
        (observationLinearTree j)
      change ((_ ×ₖ _) ∘ₖ _).map (observationLinearSpin j ∘ Prod.snd) = _
      rw [Kernel.map_comp, Kernel.map_comp_right _ measurable_snd
        (measurable_observationLinearSpin j), ←Kernel.snd_eq, Kernel.snd_prod, ih,
        finiteStateCascadeGibbsKernel_succ]

theorem nativeStreamingObservationTerminalSpinKernel_scheme_energy
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (j : ℕ) (hj : j≤k+2) :
    anisotropicObservationTerminalSpinKernel D (Paper.parisiSchemeMeasure s)
      (anisotropicRecordedSchemeSchedule s j) =
      (finiteStateCascadeGibbsKernel (fun _ : Configuration n => 0)
        (anisotropicSchemeMass s)
        (fun l => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) j).comap
          (anisotropicObservationEnergy D) (measurable_anisotropicObservationEnergy D) := by
  have he := anisotropicRecordedProfileTreeKernel_scheme_energy D s (observationLinearTree j) hj
  have hs := congrArg (fun K : Kernel (AnisotropicObservationState n)
      (Records (FiniteStateField (Configuration n)) (Configuration n) (observationLinearTree j)) =>
      K.map (observationLinearSpin j)) he
  rw [←Kernel.map_comp_right _
    (measurable_observationTreeMap _ (measurable_anisotropicObservationEnergy D) _)
    (measurable_observationLinearSpin j)] at hs
  have hf : observationLinearSpin (E:=FiniteStateField (Configuration n))
      (S:=Configuration n) j ∘
      observationTreeMap (S:=Configuration n) (anisotropicObservationEnergy D)
        (observationLinearTree j) =
      observationLinearSpin (E:=AnisotropicObservationState n) (S:=Configuration n) j := by
    funext z
    exact nativeStreamingObservationLinearSpin_treeMap
      (S:=Configuration n) (anisotropicObservationEnergy D) j z
  rw [hf, ←Kernel.comap_map_comm _ (measurable_anisotropicObservationEnergy D)
    (measurable_observationLinearSpin j), nativeStreamingFiniteObservationLinearKernel_spin] at hs
  have hzero : anisotropicRecordedSchemeSchedule s 0=1 := by
    apply Subtype.ext
    rw [anisotropicRecordedSchemeSchedule, Nat.sub_zero,
      anisotropicFiniteMeshNode_coe s _ le_rfl, s.q_top]
    rfl
  rw [anisotropicRecordedLinearSpinKernel D (Paper.parisiSchemeMeasure s)
    (anisotropicRecordedSchemeSchedule s) hzero j
    (fun i _ => anisotropicRecordedSchemeSchedule_antitone s (Nat.le_succ i))] at hs
  exact hs

end QuantitativeFollowup
