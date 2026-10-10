module
public import FourPapersCommon.FiniteCascadeGaussianRowRecords
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-! Exact pushforward of the normalized Gaussian row to its physical
retained field/spin records, including all conditional-mark vertices. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
variable {S I J : Type} [Fintype S] [Fintype I] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def finiteCascadeGaussianRowPhysicalRecords (K : FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (z : ℝ × (FiniteStateField S × Records (FiniteStateField S) S T)) :=
  (z.2.1+z.1 • K,finiteCascadeShiftRecords K z.1 T z.2.2)

theorem measurable_finiteCascadeGaussianRowPhysicalRecords (K : FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    Measurable (finiteCascadeGaussianRowPhysicalRecords K T) :=
  ((measurable_fst.comp measurable_snd).add (measurable_fst.smul_const K)).prodMk
    ((measurable_finiteCascadeShiftRecords_joint K T).comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))

theorem finiteCascadeTreeGaussianRowLaw_physical_records_map (V : S → ℝ)
    (K : FiniteStateField S) (a : ℕ → ℝ) (ha : ∀j,0 ≤ a j)
    (hanti : Antitone a) (h0 : a 0 ≤ 1)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (s c : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (hs : s ≤ finiteCascadeTreeRootCoefficient a T)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S)
    (B : ℝ) (hB : 0 ≤ B) (hK : ∀σ,|K σ| ≤ B) :
    (finiteCascadeTreeGaussianRowLaw V K a L s (c^2) T R H).map
      (finiteCascadeGaussianRowPhysicalRecords K T) =
      finiteCascadeTreeGaussianJointLaw V a L s T
        (finiteStateGaussianSumMap R (scalarGaussianShift (c • K))) H := by
  have := finiteCascadeTreeGaussianRowLaw_probability V K a ha hanti h0 L s (c^2)
    T hs R H B hB hK
  have := finiteCascadeTreeGaussianJointLaw_probability V a ha L s T
    (finiteStateGaussianSumMap R (scalarGaussianShift (c • K))) H
  have hm := measurable_finiteCascadeGaussianRowPhysicalRecords K T
  ext A hA
  have hb (z : FiniteStateField S × Records (FiniteStateField S) S T) :
      |A.indicator (fun _ => (1:ℝ)) z| ≤ 1 := by
    by_cases hz : z∈A <;> simp [hz]
  have he := integral_finiteCascadeTreeGaussianRowLaw_physical_records V K a ha hanti h0 L
    s c T hs R H B hB hK (A.indicator (fun _ => (1:ℝ)))
    (measurable_const.indicator hA) 1 (by norm_num) hb
  change (∫z,A.indicator (fun _ => (1:ℝ)) (finiteCascadeGaussianRowPhysicalRecords K T z)
    ∂finiteCascadeTreeGaussianRowLaw V K a L s (c^2) T R H) = _ at he
  rw [← integral_map hm.aemeasurable (measurable_const.indicator hA).aestronglyMeasurable] at he
  change (∫z,A.indicator (1 : FiniteStateField S × Records (FiniteStateField S) S T → ℝ) z
    ∂(finiteCascadeTreeGaussianRowLaw V K a L s (c^2) T R H).map
      (finiteCascadeGaussianRowPhysicalRecords K T)) =
    ∫z,A.indicator (1 : FiniteStateField S × Records (FiniteStateField S) S T → ℝ) z
      ∂finiteCascadeTreeGaussianJointLaw V a L s T
        (finiteStateGaussianSumMap R (scalarGaussianShift (c • K))) H at he
  rw [integral_indicator_one hA,integral_indicator_one hA] at he
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp he

end FourPapersCommon
