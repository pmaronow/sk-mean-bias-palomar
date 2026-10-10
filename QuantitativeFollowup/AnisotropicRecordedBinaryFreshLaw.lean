module
public import QuantitativeFollowup.AnisotropicRecordedFreshTerminalLaw
public import QuantitativeFollowup.AnisotropicRecordedNativeMarginal
public import QuantitativeFollowup.AnisotropicRecordedMovingLawConvergence

@[expose] public section

/-! A binary native genealogy has precisely the law of two fresh conditional
terminal spins. Both endpoints of the split clock and atoms are included. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ}
set_option maxHeartbeats 650000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def anisotropicBinaryObservationSchedule (p : Paper.Overlap) : ℕ→Paper.Overlap
  | 0 => 1
  | 1 => p
  | _ => 0

def anisotropicBinaryObservationTree : FiniteTerminalGenealogy 2 :=
  .advance (.fork (.advance .leaf) (.advance .leaf))

def anisotropicBinaryObservationSpins :
    Records (AnisotropicObservationState n) (Configuration n) anisotropicBinaryObservationTree→
      Configuration n×Configuration n := fun z=>(z.2.1.2,z.2.2.2)

theorem measurable_anisotropicBinaryObservationSpins :
    Measurable (anisotropicBinaryObservationSpins (n:=n)) :=
  measurable_snd.fst.snd.prodMk measurable_snd.snd.snd

theorem continuous_anisotropicBinaryObservationSpins :
    Continuous (anisotropicBinaryObservationSpins (n:=n)) :=
  continuous_snd.fst.snd.prodMk continuous_snd.snd.snd

theorem anisotropicBinaryObservationTree_spin_kernel (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (p : Paper.Overlap) :
    (anisotropicRecordedProfileTreeKernel D μ (anisotropicBinaryObservationSchedule p)
      anisotropicBinaryObservationTree).map anisotropicBinaryObservationSpins=
      ((anisotropicObservationTerminalSpinKernel D μ p) ×ₖ
        (anisotropicObservationTerminalSpinKernel D μ p)) ∘ₖ anisotropicObservationTransition D μ 0 p := by
  let K:=((anisotropicTerminalSpinKernel D).comap (anisotropicObservationParameter D)
    (measurable_anisotropicObservationParameter D))
  let A:=(Kernel.id ×ₖ K) ∘ₖ anisotropicObservationTransition D μ p 1
  change ((Kernel.id ×ₖ (A ×ₖ A)) ∘ₖ anisotropicObservationTransition D μ 0 p).map
    ((Prod.map Prod.snd Prod.snd) ∘ Prod.snd)=_
  rw [Kernel.map_comp,Kernel.map_comp_right _ measurable_snd (measurable_snd.prodMap measurable_snd),
    ←Kernel.snd_eq,Kernel.snd_prod,←Kernel.map_prod_map _ _ measurable_snd measurable_snd]
  have hA : A.map Prod.snd=anisotropicObservationTerminalSpinKernel D μ p := by
    rw [←Kernel.snd_eq]
    change ((Kernel.id ×ₖ K) ∘ₖ anisotropicObservationTransition D μ p 1).snd=_
    rw [Kernel.snd_comp,Kernel.snd_prod]
    rfl
  rw [hA]

theorem anisotropicBinaryObservationTree_spin_law (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) :
    (anisotropicRecordedProfileTreeLaw D μ a (anisotropicBinaryObservationSchedule p)
      anisotropicBinaryObservationTree).map (anisotropicBinaryObservationSpins ∘ Prod.snd)=
      (anisotropicFreshTerminalPairLaw D μ a p).snd := by
  rw [anisotropicRecordedProfileTreeLaw,Measure.compProd_eq_comp_prod,
    Measure.map_comp _ _ (measurable_anisotropicBinaryObservationSpins.comp measurable_snd),
    Kernel.map_comp_right _ measurable_snd measurable_anisotropicBinaryObservationSpins,
    ←Kernel.snd_eq,Kernel.snd_prod,anisotropicBinaryObservationTree_spin_kernel,
    ←Measure.comp_assoc,←anisotropicNativeObservation_law,
    anisotropicFreshTerminalPairLaw_pair_marginal]

def anisotropicBinarySpinProbability (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) :
    ProbabilityMeasure (Configuration n×Configuration n) :=
  (anisotropicRecordedProfileProbability D μ a (anisotropicBinaryObservationSchedule p)
    anisotropicBinaryObservationTree).map (anisotropicBinaryObservationSpins ∘ Prod.snd)

theorem anisotropicBinarySpinProbability_eq_fresh_pair (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) :
    (anisotropicBinarySpinProbability D μ a p : Measure _)=
      (anisotropicFreshTerminalPairLaw D μ a p).snd :=
  anisotropicBinaryObservationTree_spin_law D μ a p

theorem tendsto_anisotropicBinarySpinProbability {L : Type*} {l : Filter L} [l.IsCountablyGenerated]
    (D : AnisotropicSpinModel n) {μ : L→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) (a : ℝ) {p : L→Paper.Overlap} {r : Paper.Overlap}
    (hp : Tendsto p l (𝓝 r)) :
    Tendsto (fun j=>anisotropicBinarySpinProbability D (μ j) a (p j)) l
      (𝓝 (anisotropicBinarySpinProbability D ν a r)) := by
  have hq (i : ℕ) (_hi : i≤2) : Tendsto
      (fun j=>anisotropicBinaryObservationSchedule (p j) i) l
      (𝓝 (anisotropicBinaryObservationSchedule r i)) := by
    rcases i with _|i
    · exact tendsto_const_nhds
    rcases i with _|i
    · exact hp
    · exact tendsto_const_nhds
  have hmono (u : Paper.Overlap) (i : ℕ) (hi : i<2) :
      anisotropicBinaryObservationSchedule u (i+1)≤anisotropicBinaryObservationSchedule u i := by
    have hi' : i=0∨i=1:=by omega
    rcases hi' with rfl|rfl
    · exact u.property.2
    · exact u.property.1
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (tendsto_anisotropicRecordedProfileProbability_moving_schedule D hμ a
      (fun j=>anisotropicBinaryObservationSchedule (p j)) (anisotropicBinaryObservationSchedule r)
      anisotropicBinaryObservationTree hq (fun j=>hmono (p j)) (hmono r))
    (continuous_anisotropicBinaryObservationSpins.comp continuous_snd)

theorem continuous_anisotropicBinarySpinProbability_split (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) : Continuous (anisotropicBinarySpinProbability D μ a) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  exact tendsto_anisotropicBinarySpinProbability D (tendsto_const_nhds (x:=μ)) a
    (tendsto_id : Tendsto (fun p : Paper.Overlap=>p) (𝓝 r) (𝓝 r))

end QuantitativeFollowup
