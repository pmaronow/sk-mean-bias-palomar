module
public import FourPapersCommon.FiniteCascadeTreeReferenceLinearFields

@[expose] public section

/-! The actual normalized marked tree law as a density on a fixed independent
Gaussian-coordinate space and terminal counting spins. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
attribute [local instance] isFiniteMeasure_terminalSpinCountingLaw
variable {S I J : Type} [Fintype S] [Fintype I] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

def finiteCascadeTreeGaussianRecordDensity (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (s : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S)
    (p : FiniteStateField S × Records (FiniteStateField S) S T) : ℝ :=
  Real.exp (s * finiteStateGaussianTerminalCascade V a L j p.1 +
    finiteCascadeTreeLogDensity V a L T p.1 p.2) /
      finiteCascadeTreeGaussianNormalizer V a L s j R H

def finiteCascadeTreeGaussianFlatDensity (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (s : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S) :=
  finiteCascadeTreeGaussianRecordDensity V a L s T R H ∘
    finiteCascadeTreeReferenceRootFlatRecord L T R H

def finiteCascadeTreeGaussianFlatReferenceMeasure {j : ℕ} (T : FiniteTerminalGenealogy j) :
    Measure (FiniteStateGaussianInput (J ⊕ GaussianCoordinateIndex I T) × TerminalSpins S T) :=
  (stdGaussian (FiniteStateGaussianInput (J ⊕ GaussianCoordinateIndex I T))).prod
    (terminalSpinCountingLaw S T)

theorem measurable_finiteCascadeTreeGaussianRecordDensity (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (s : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S) :
    Measurable (finiteCascadeTreeGaussianRecordDensity V a L s T R H) :=
  ((((contDiff_one_finiteStateGaussianTerminalCascade V a ha L j).continuous.measurable.comp
    measurable_fst).const_mul s).add (measurable_finiteCascadeTreeLogDensity V a ha L T)).exp.div_const _

theorem measurable_finiteCascadeTreeGaussianFlatDensity (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (s : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S) :
    Measurable (finiteCascadeTreeGaussianFlatDensity V a L s T R H) :=
  (measurable_finiteCascadeTreeGaussianRecordDensity V a ha L s T R H).comp
    (measurable_finiteCascadeTreeReferenceRootFlatRecord L T R H)

theorem finiteCascadeTreeGaussianFlatDensity_pos (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (s : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S)
    (p : FiniteStateGaussianInput (J ⊕ GaussianCoordinateIndex I T) × TerminalSpins S T) :
    0 < finiteCascadeTreeGaussianFlatDensity V a L s T R H p :=
  div_pos (Real.exp_pos _) (finiteCascadeTreeGaussianNormalizer_pos V a ha L s j R H)

theorem finiteCascadeTreeGaussianJointLaw_eq_flat_density (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (s : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S) :
    ((finiteCascadeTreeGaussianFlatReferenceMeasure (S:=S) (I:=I) (J:=J) T).withDensity
      (fun p => ENNReal.ofReal (finiteCascadeTreeGaussianFlatDensity V a L s T R H p))).map
      (finiteCascadeTreeReferenceRootFlatRecord L T R H) =
      finiteCascadeTreeGaussianJointLaw V a L s T R H := by
  dsimp only [finiteCascadeTreeGaussianFlatDensity,Function.comp_def,
    finiteCascadeTreeGaussianFlatReferenceMeasure]
  rw [map_withDensity_pullback _ _
    (measurable_finiteCascadeTreeReferenceRootFlatRecord L T R H) _
    (measurable_finiteCascadeTreeGaussianRecordDensity V a ha L s T R H).ennreal_ofReal]
  rw [finiteCascadeTreeGaussianReferenceLaw_eq_flat_gaussian,
    finiteCascadeTreeGaussianJointLaw_density V a ha L s T R H]
  congr 1
  funext p
  simp only [finiteCascadeTreeGaussianRecordDensity,finiteCascadeTreeLogDensity_add_root_eq]

theorem isProbabilityMeasure_finiteCascadeTreeGaussianFlatDensity (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (s : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S) :
    IsProbabilityMeasure
      ((finiteCascadeTreeGaussianFlatReferenceMeasure (S:=S) (I:=I) (J:=J) T).withDensity
        (fun p => ENNReal.ofReal (finiteCascadeTreeGaussianFlatDensity V a L s T R H p))) := by
  haveI := finiteCascadeTreeGaussianJointLaw_probability V a ha L s T R H
  have hm := finiteCascadeTreeGaussianJointLaw_eq_flat_density V a ha L s T R H
  haveI : IsProbabilityMeasure
      (((finiteCascadeTreeGaussianFlatReferenceMeasure (S:=S) (I:=I) (J:=J) T).withDensity
        (fun p => ENNReal.ofReal (finiteCascadeTreeGaussianFlatDensity V a L s T R H p))).map
        (finiteCascadeTreeReferenceRootFlatRecord L T R H)) := by rw [hm]; infer_instance
  exact Measure.isProbabilityMeasure_of_map
    (measurable_finiteCascadeTreeReferenceRootFlatRecord L T R H).aemeasurable

theorem integrable_finiteCascadeTreeGaussianFlatDensity (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (s : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S) :
    Integrable (finiteCascadeTreeGaussianFlatDensity V a L s T R H)
      (finiteCascadeTreeGaussianFlatReferenceMeasure (S:=S) (I:=I) (J:=J) T) := by
  haveI := isProbabilityMeasure_finiteCascadeTreeGaussianFlatDensity V a ha L s T R H
  refine ⟨(measurable_finiteCascadeTreeGaussianFlatDensity V a ha L s T R H).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (.of_forall fun p =>
    (finiteCascadeTreeGaussianFlatDensity_pos V a ha L s T R H p).le)]
  have hn : ((finiteCascadeTreeGaussianFlatReferenceMeasure (S:=S) (I:=I) (J:=J) T).withDensity
      (fun p => ENNReal.ofReal (finiteCascadeTreeGaussianFlatDensity V a L s T R H p))) Set.univ = 1 :=
    measure_univ
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ] at hn
  rw [hn]
  exact ENNReal.one_lt_top

theorem integral_finiteCascadeTreeGaussianJointLaw_eq_flat_density (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (s : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S)
    (F : FiniteStateField S × Records (FiniteStateField S) S T → ℝ) (hF : Measurable F) :
    (∫p,F p ∂finiteCascadeTreeGaussianJointLaw V a L s T R H) =
      ∫p,finiteCascadeTreeGaussianFlatDensity V a L s T R H p *
        F (finiteCascadeTreeReferenceRootFlatRecord L T R H p)
        ∂finiteCascadeTreeGaussianFlatReferenceMeasure (S:=S) (I:=I) (J:=J) T := by
  rw [←finiteCascadeTreeGaussianJointLaw_eq_flat_density V a ha L s T R H,
    integral_map (measurable_finiteCascadeTreeReferenceRootFlatRecord L T R H).aemeasurable
      hF.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_finiteCascadeTreeGaussianFlatDensity V a ha L s T R H).ennreal_ofReal
      (.of_forall fun _ => ENNReal.ofReal_lt_top) _]
  apply integral_congr_ae
  exact .of_forall fun p => by
    dsimp only
    rw [ENNReal.toReal_ofReal (finiteCascadeTreeGaussianFlatDensity_pos V a ha L s T R H p).le]
    rfl

theorem integral_finiteCascadeTreeGaussianFlatDensity_one (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (s : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S) :
    (∫p,finiteCascadeTreeGaussianFlatDensity V a L s T R H p
      ∂finiteCascadeTreeGaussianFlatReferenceMeasure (S:=S) (I:=I) (J:=J) T) = 1 := by
  haveI := finiteCascadeTreeGaussianJointLaw_probability V a ha L s T R H
  simpa using (integral_finiteCascadeTreeGaussianJointLaw_eq_flat_density V a ha L s T R H
    (fun _ => 1) measurable_const).symm

end FourPapersCommon
