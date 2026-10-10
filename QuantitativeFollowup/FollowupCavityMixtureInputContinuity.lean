module
public import FourPapersCommon.GenericFiniteStateCascadeEndpointContinuity
public import FourPapersCommon.FiniteStateCascadeAllJets
public import FourPapersCommon.JointDerivativeContinuity

@[expose] public section

/-! Genuine joint continuity under varying Gaussian input maps, including
singular maps. Spatial derivative continuity follows from the actual
uniform posterior jet bounds, without differentiating the parameter. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped ContDiff Topology
namespace QuantitativeFollowup
variable {S : Type} {P : Type*} [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S]
  [TopologicalSpace P] [FirstCountableTopology P] {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem continuous_cavityCascade_input_family
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0 ≤ a i)
    (L : P→ℕ→Field n→L[ℝ]FiniteStateField S)
    (hL : ∀j,Continuous (fun p=>L p j)) (N : ℕ) :
    Continuous (fun z : P×FiniteStateField S=>
      finiteStateGaussianTerminalCascade V a (L z.1) N z.2) := by
  induction N with
  | zero =>
    exact (SpinGlass.AT.contDiff_gtStateLogPartition V).continuous.comp continuous_snd
  | succ N ih =>
    change Continuous (fun z : P×FiniteStateField S=>finiteStateGaussianStep (a N)
      (L z.1 N) (finiteStateGaussianTerminalCascade V a (L z.1) N) z.2)
    exact continuous_finiteStateGaussianStep_family (a N)
      (fun z : P×FiniteStateField S=>fun H=>finiteStateGaussianTerminalCascade V a (L z.1) N H)
      (ih.comp ((continuous_fst.fst).prodMk continuous_snd)) 1
      (fun z=>finiteStateGaussianTerminalCascade_lipschitz V a ha (L z.1) N)
      (fun z : P×FiniteStateField S=>L z.1 N) ((hL N).comp continuous_fst)
      (fun z : P×FiniteStateField S=>z.2) continuous_snd

theorem continuous_cavityCascade_input_spatial_jets
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0 ≤ a i) (ha1 : a 0 ≤ 1) (hdec : Antitone a)
    (L : P→ℕ→Field n→L[ℝ]FiniteStateField S)
    (hL : ∀j,Continuous (fun p=>L p j)) (N r : ℕ) :
    Continuous (fun z : P×FiniteStateField S=>
      iteratedFDeriv ℝ r (finiteStateGaussianTerminalCascade V a (L z.1) N) z.2) := by
  exact continuous_iteratedFDeriv_family_of_uniform_jet_bounds _
    (continuous_cavityCascade_input_family V a ha L hL N)
    (fun p=>contDiff_finiteStateGaussianTerminalCascade V a ha (L p) N)
    (finiteStateSpatialJetBound S n) (finiteStateSpatialJetBound_nonneg S n)
    (fun j hj p H=>norm_finiteStateCascade_jet_le_uniform V a ha ha1 hdec (L p) N j
      (by omega) H) r

theorem continuous_cavityCascade_input_fderiv
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0 ≤ a i) (ha1 : a 0 ≤ 1) (hdec : Antitone a)
    (L : P→ℕ→Field n→L[ℝ]FiniteStateField S)
    (hL : ∀j,Continuous (fun p=>L p j)) (N : ℕ) :
    Continuous (fun z : P×FiniteStateField S=>
      fderiv ℝ (finiteStateGaussianTerminalCascade V a (L z.1) N) z.2) :=
  continuous_fderiv_family_of_uniform_secondJet _
    (continuous_cavityCascade_input_family V a ha L hL N)
    (fun p=>contDiff_finiteStateGaussianTerminalCascade V a ha (L p) N)
    (finiteStateSpatialJetBound S n 2) (finiteStateSpatialJetBound_nonneg S n 2)
    (fun p H=>norm_finiteStateCascade_jet_le_uniform V a ha ha1 hdec (L p) N 2 (by omega) H)

end QuantitativeFollowup
