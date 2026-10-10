module
public import FourPapersCommon.FiniteCascadeTreeGaussianDensity
public import Mathlib.Probability.Kernel.Composition.Lemmas

@[expose] public section

/-! Removing a genuine zero-noise root edge changes neither the spin law
nor the Gaussian root tilt. This removes the dummy zero-mass cell before
the physical genealogy is assigned nonnegative vertex charges. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace FiniteTerminalGenealogy

@[reducible] def trimRoot : {j : ℕ} → FiniteTerminalGenealogy j →
    FiniteTerminalGenealogy (j-1)
  | _, .leaf => .leaf
  | _, .advance T => T
  | _, .fork T U => .fork (trimRoot T) (trimRoot U)

@[reducible] def trimRecords {E S : Type} : {j : ℕ} → (T : FiniteTerminalGenealogy j) →
    Records E S T → Records E S (trimRoot T)
  | _, .leaf => id
  | _, .advance _ => Prod.snd
  | _, .fork T U => Prod.map (trimRecords (E:=E) (S:=S) T) (trimRecords U)

theorem measurable_trimRecords {E S : Type} [MeasurableSpace E] [MeasurableSpace S]
    {j : ℕ} (T : FiniteTerminalGenealogy j) : Measurable (trimRecords (E:=E) (S:=S) T) := by
  induction T with
  | leaf => exact measurable_id
  | advance T => exact measurable_snd
  | fork T U ihT ihU => exact ihT.prodMap ihU

theorem leafCount_trimRoot {j : ℕ} (T : FiniteTerminalGenealogy j) :
    FiniteCascadeGenealogy.leafCount (asGenealogy (trimRoot T)) =
      FiniteCascadeGenealogy.leafCount (asGenealogy T) := by
  induction T with
  | leaf => rfl
  | advance T => rfl
  | fork T U ihT ihU => exact congrArg₂ (·+·) ihT ihU

@[reducible] def trimmedSpinEquiv {S : Type} [MeasurableSpace S] :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) →
      FiniteCascadeGenealogy.Samples S (asGenealogy (trimRoot T)) ≃ᵐ
        FiniteCascadeGenealogy.Samples S (asGenealogy T)
  | _, .leaf => MeasurableEquiv.refl _
  | _, .advance T => MeasurableEquiv.refl _
  | _, .fork T U => (trimmedSpinEquiv T).prodCongr (trimmedSpinEquiv U)

theorem trimmedSpinEquiv_spins {E S : Type} [MeasurableSpace E] [MeasurableSpace S]
    {j : ℕ} (T : FiniteTerminalGenealogy j) (z : Records E S T) :
    trimmedSpinEquiv (S:=S) T (spins (trimRoot T) (trimRecords T z)) = spins T z := by
  induction T with
  | leaf => rfl
  | advance T => rfl
  | fork T U ihT ihU => exact congrArg₂ Prod.mk (ihT z.1) (ihU z.2)

end FiniteTerminalGenealogy

variable {S I J : Type} [Fintype S] [Fintype I] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

theorem finiteStateGaussianRawKernel_zero :
    finiteStateGaussianRawKernel (0 : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) =
      Kernel.id := by
  ext H B hB
  rw [finiteStateGaussianRawKernel_apply]
  simp [Measure.map_const,Kernel.id_apply]

theorem finiteStateGaussianTerminalCascade_zero_root_step (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j : ℕ) (hL : L j=0) :
    finiteStateGaussianTerminalCascade V a L (j+1) =
      finiteStateGaussianTerminalCascade V a L j := by
  funext H
  change finiteStateGaussianStep _ _ _ H = _
  rw [hL]
  simp only [finiteStateGaussianStep,zero_apply,add_zero]
  by_cases ha : a j=0
  · simp [OverlapPaper.sourceLogAverage,ha,finiteStateGaussianTerminalCascade]
  · simp [OverlapPaper.sourceLogAverage,ha,finiteStateGaussianTerminalCascade]

theorem finiteStateGaussianCascadeKernel_zero_root_step (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j,0≤a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j : ℕ) (hL : L j=0) :
    finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) j = Kernel.id := by
  classical
  ext H B hB
  unfold finiteStateGaussianCascadeKernel
  rw [finiteStateGaussianStepKernel_apply _ _ _
    (show Measurable (finiteStateGaussianCascade a L (gtStateLogPartition V) j) from
      (contDiff_one_finiteStateGaussianTerminalCascade V a ha L j).continuous.measurable)]
  simp only [finiteStateGaussianStepLaw,hL,finiteStateGaussianRawKernel_zero,Kernel.id_apply]
  simp only [Measure.tilted,integral_dirac]
  rw [withDensity_apply _ hB,setLIntegral_dirac]
  simp [Real.exp_ne_zero,Set.indicator_apply]

theorem finiteCascadeTreeRecordKernel_trimRoot (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j,0≤a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hj : 0<j) (hL : L (j-1)=0) :
    (finiteCascadeTreeRecordKernel V a L T).map (trimRecords T) =
      finiteCascadeTreeRecordKernel V a L (trimRoot T) := by
  induction T with
  | leaf => omega
  | @advance j T =>
      haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
      change ((_ ×ₖ _) ∘ₖ _).map Prod.snd = _
      rw [Kernel.map_comp,←Kernel.snd_eq,Kernel.snd_prod,
        finiteStateGaussianCascadeKernel_zero_root_step V a ha L j hL,Kernel.comp_id]
  | fork T U ihT ihU =>
      haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
      haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L U
      change (_ ×ₖ _).map (Prod.map _ _) = _ ×ₖ _
      rw [←Kernel.map_prod_map _ _ (measurable_trimRecords T) (measurable_trimRecords U),
        ihT hj hL,ihU hj hL]

theorem finiteCascadeTreeRootCoefficient_previous_ge (a : ℕ → ℝ)
    (ha : ∀ j,0≤a j) {j : ℕ} (T : FiniteTerminalGenealogy j) (hj : 0<j) :
    a (j-1) ≤ finiteCascadeTreeRootCoefficient a T := by
  induction T with
  | leaf => omega
  | advance T => exact le_rfl
  | @fork j T U ihT ihU =>
      change a (j-1) ≤ finiteCascadeTreeRootCoefficient a T + finiteCascadeTreeRootCoefficient a U
      linarith [ihT hj,ihU hj,ha (j-1)]

theorem finiteCascadeTreeCharges_nonneg_of_root_le (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (hs : s≤finiteCascadeTreeRootCoefficient a T) (H : FiniteStateField S)
    (z : Records (FiniteStateField S) S T) :
    ∀c∈finiteCascadeTreeCharges V a L s T H z,0≤c.1 := by
  intro c hc
  rcases List.mem_cons.mp hc with h|h
  · subst c; exact sub_nonneg.mpr hs
  · exact finiteCascadeTreeInteriorCharges_nonneg V a ha hanti h0 L T z c h

theorem finiteCascadeTreeGaussianJointLaw_trimRoot (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j,0≤a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (s : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy (j+1)) (hL : L j=0)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S) :
    (finiteCascadeTreeGaussianJointLaw V a L s T R H).map
      (Prod.map id (trimRecords T)) =
        finiteCascadeTreeGaussianJointLaw V a L s (trimRoot T) R H := by
  haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
  haveI := isProbabilityMeasure_tilted
    (integrable_exp_finiteCascadeTreeGaussianInitial V a ha L s (j+1) R H)
  unfold finiteCascadeTreeGaussianJointLaw
  rw [←Measure.compProd_map (measurable_trimRecords T),
    finiteCascadeTreeRecordKernel_trimRoot V a ha L T (by omega) hL,
    finiteStateGaussianTerminalCascade_zero_root_step V a L j hL]
  rfl

theorem finiteCascadeTreeGaussianJointLaw_trimmed_spin_marginal
    (V : S → ℝ) (a : ℕ → ℝ) (ha : ∀j,0≤a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (s : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy (j+1)) (hL : L j=0)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S) :
    (finiteCascadeTreeGaussianJointLaw V a L s (trimRoot T) R H).map
      (fun z : FiniteStateField S × Records (FiniteStateField S) S (trimRoot T) =>
        (trimmedSpinEquiv (S:=S) T).toEquiv.toFun (spins (trimRoot T) z.2)) =
        (finiteCascadeTreeGaussianJointLaw V a L s T R H).map (fun z => spins T z.2) := by
  rw [←finiteCascadeTreeGaussianJointLaw_trimRoot V a ha L s T hL R H,
    Measure.map_map (show Measurable (fun z : FiniteStateField S × Records (FiniteStateField S) S (trimRoot T) =>
        (trimmedSpinEquiv (S:=S) T).toEquiv.toFun (spins (trimRoot T) z.2)) from
        (trimmedSpinEquiv (S:=S) T).measurable.comp
          ((measurable_spins (trimRoot T)).comp measurable_snd))
      (measurable_id.prodMap (measurable_trimRecords T))]
  congr 1
  funext z
  exact trimmedSpinEquiv_spins T z.2

end FourPapersCommon
