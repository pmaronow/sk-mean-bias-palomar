module
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeSquareBounds
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeHistory

@[expose] public section

/-! The true finite posterior field score as an observable of the retained
energy history and terminal spin. Its law is transported without dropping
the terminal draw. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT
variable {S : Type} [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n k : ℕ}
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128

def cascadePosteriorRecordedMean (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j i : ℕ) (K : FiniteStateField S)
    (h : FiniteHistory (FiniteStateField S) j) : ℝ :=
  fderiv ℝ (finiteStateGaussianTerminalCascade V a L (j-i)) (historyExtended h i) K

def cascadePosteriorScoreTime (N : ℕ) : Option (Option (Fin N))→ℕ
  | none=>N+1
  | some none=>0
  | some (some i)=>i+1

def cascadePosteriorRecordedScore (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (N : ℕ) (W : FiniteStateField S)
    (z : FiniteHistory (FiniteStateField S) (N+1)×S) : ℝ :=
  W z.2-∑i,cascadePosteriorStieltjesWeight a N i*
    cascadePosteriorRecordedMean V a L (N+1) (cascadePosteriorScoreTime N i) W z.1

theorem fderiv_cascadePosteriorHistoryPotential_apply (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S)
    (j i : ℕ) (H W : FiniteStateField S) (z : Fin j→Field n) :
    fderiv ℝ (fun Q=>cascadePosteriorHistoryPotential V a L j i Q z) H W=
      cascadePosteriorRecordedMean V a L j i W (cascadePosteriorHistory L j H z) := by
  rw [cascadePosteriorHistoryPotential_eq_translate]
  let U:=finiteStateGaussianTerminalCascade V a L (j-i)
  let w:=cascadePosteriorHistory L j 0 z (Fin.ofNat (j+1) i)
  have hd:=((contDiff_finiteStateGaussianTerminalCascade V a ha L (j-i)).differentiable
    (by simp) (H+w)).hasFDerivAt.comp H ((hasFDerivAt_id H).add_const w)
  change fderiv ℝ (fun Q=>U (Q+w)) H W=_
  have he : fderiv ℝ (fun Q=>U (Q+w)) H=
      (fderiv ℝ U (H+w)).comp (ContinuousLinearMap.id ℝ _) := by
    simpa only [Function.comp_def,id_eq,U,w] using hd.fderiv
  rw [he]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply]
  unfold cascadePosteriorRecordedMean
  dsimp only [historyExtended]
  rw [cascadePosteriorHistory_eq_initial_add]

theorem cavityFinitePosteriorScore_eq_recorded (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S)
    (N : ℕ) (H W : FiniteStateField S) (z : (Fin (N+1)→Field n)×S) :
    cavityFinitePosteriorScore V a L N H W z=
      cascadePosteriorRecordedScore V a L N W
        (cascadePosteriorHistory L (N+1) H z.1,z.2) := by
  unfold cavityFinitePosteriorScore cascadePosteriorRecordedScore
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  cases i with
  | none=>exact fderiv_cascadePosteriorHistoryPotential_apply V a ha L (N+1) (N+1) H W z.1
  | some i=>
    cases i with
    | none=>exact fderiv_cascadePosteriorHistoryPotential_apply V a ha L (N+1) 0 H W z.1
    | some i=>exact fderiv_cascadePosteriorHistoryPotential_apply V a ha L (N+1) (i+1) H W z.1

theorem measurable_cascadePosteriorRecordedScore (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S)
    (N : ℕ) (W : FiniteStateField S) :
    Measurable (cascadePosteriorRecordedScore V a L N W) := by
  have hm (i : ℕ) : Measurable (cascadePosteriorRecordedMean V a L (N+1) i W) := by
    exact ((((contDiff_finiteStateGaussianTerminalCascade V a ha L (N+1-i)).fderiv_right
      (m:=∞) (by simp)).continuous.comp (continuous_apply (Fin.ofNat (N+2) i))).clm_apply
        continuous_const).measurable
  exact ((measurable_of_finite W).comp measurable_snd).sub
    (Finset.measurable_sum _ fun i _=>measurable_const.mul ((hm _).comp measurable_fst))

theorem integral_anisotropicFiniteRestart_marked_record (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n)
    (f : FiniteHistory (FiniteStateField (Configuration n)) (k+2)×Configuration n→ℝ)
    (hf : Measurable f) :
    (∫z,f (cascadePosteriorHistory
      (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D (vectorClampedScheme s q q.property) l))
      (k+2) (anisotropicEnergyMap D (anisotropicDisorderInjection n g+anisotropicUnitInput D x)) z.1,z.2)
      ∂cascadePosteriorGaussianLaw (fun _ : Configuration n=>0)
        (anisotropicSchemeMass (vectorClampedScheme s q q.property))
        (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D (vectorClampedScheme s q q.property) l))
        (k+2) (anisotropicEnergyMap D (anisotropicDisorderInjection n g+anisotropicUnitInput D x)))=
      ∫z,f (anisotropicFiniteRestartEnergyHistory D s g q x z.1,z.2)
        ∂anisotropicFiniteRestartMarkedLaw D s g q x := by
  let cs:=vectorClampedScheme s q q.property
  let L:=fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D cs l)
  let H:=anisotropicEnergyMap D (anisotropicDisorderInjection n g+anisotropicUnitInput D x)
  have hG:=integral_map (μ:=cascadePosteriorGaussianLaw (fun _ : Configuration n=>0)
      (anisotropicSchemeMass cs) L (k+2) H)
    (measurable_cascadePosteriorCoordinateMap L (k+2) H).aemeasurable hf.aestronglyMeasurable
  rw [cascadePosteriorGaussianLaw_map _ _ (anisotropicSchemeMass_nonneg cs)] at hG
  have hP:=integral_map (μ:=anisotropicFiniteRestartMarkedLaw D s g q x)
    ((measurable_anisotropicFiniteRestartEnergyHistory D s g q x).prodMap measurable_id).aemeasurable hf.aestronglyMeasurable
  rw [anisotropicFiniteRestartMarkedLaw_posterior_map D s g q x] at hP
  exact hG.symm.trans hP

end QuantitativeFollowup
