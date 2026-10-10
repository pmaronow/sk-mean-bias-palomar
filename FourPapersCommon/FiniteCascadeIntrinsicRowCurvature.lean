module
public import FourPapersCommon.FiniteCascadeGaussianRowRecordLaw
public import FourPapersCommon.FiniteCascadeTreeGaussianRowMoments

@[expose] public section

/-! Gaussian row curvature is an intrinsic observable of the actual
translated field/spin record, with the same genuine density charges. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
variable {S I : Type} [Fintype S] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem finiteCascadeShiftRecords_zero (K : FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (z : Records (FiniteStateField S) S T) :
    finiteCascadeShiftRecords K 0 T z = z := by
  induction T with
  | leaf => rfl
  | advance T ih => simp only [finiteCascadeShiftRecords,zero_smul,add_zero,ih z.2]
  | fork T U ihT ihU => exact Prod.ext (ihT z.1) (ihU z.2)

theorem spins_finiteCascadeShiftRecords (K : FiniteStateField S) (θ : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (z : Records (FiniteStateField S) S T) :
    spins T (finiteCascadeShiftRecords K θ T z) = spins T z := by
  induction T with
  | leaf => rfl
  | advance T ih => exact ih z.2
  | fork T U ihT ihU => exact Prod.ext (ihT z.1) (ihU z.2)

theorem finiteCascadeTreeTerminalFeature_shift (K M : FiniteStateField S) (θ : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (z : Records (FiniteStateField S) S T) :
    finiteCascadeTreeTerminalFeature M T (finiteCascadeShiftRecords K θ T z) =
      finiteCascadeTreeTerminalFeature M T z := by
  induction T with
  | leaf => rfl
  | advance T ih => exact ih z.2
  | fork T U ihT ihU => exact congrArg₂ (·+·) (ihT z.1) (ihU z.2)

def finiteCascadeIntrinsicRowCurvature (V : S → ℝ) (K : FiniteStateField S)
    (a : ℕ → ℝ) (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (s : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (z : FiniteStateField S × Records (FiniteStateField S) S T) : ℝ :=
  finiteCascadeTreeGaussianRowCurvature V K a L s T (0,z)

theorem measurable_finiteCascadeIntrinsicRowCurvature (V : S → ℝ) (K : FiniteStateField S)
    (a : ℕ → ℝ) (ha : ∀j,0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (s : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j) :
    Measurable (finiteCascadeIntrinsicRowCurvature V K a L s T) :=
  (measurable_finiteCascadeTreeGaussianRowCurvature V K a ha L s T).comp
    (measurable_const.prodMk measurable_id)

theorem finiteCascadeTreeGaussianRowCurvature_physical (V : S → ℝ) (K : FiniteStateField S)
    (a : ℕ → ℝ) (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (s : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (z : ℝ × (FiniteStateField S × Records (FiniteStateField S) S T)) :
    finiteCascadeTreeGaussianRowCurvature V K a L s T z =
      finiteCascadeIntrinsicRowCurvature V K a L s T
        (finiteCascadeGaussianRowPhysicalRecords K T z) := by
  simp only [finiteCascadeIntrinsicRowCurvature,finiteCascadeTreeGaussianRowCurvature,
    finiteCascadeGaussianRowPhysicalRecords,finiteCascadeTreeFeatureScore,
    finiteCascadeTreeFeatureSecondCharge,zero_smul,add_zero,
    finiteCascadeShiftRecords_zero,finiteCascadeTreeTerminalFeature_shift]

end FourPapersCommon
