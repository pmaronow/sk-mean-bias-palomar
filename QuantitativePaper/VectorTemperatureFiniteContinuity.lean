module
public import QuantitativePaper.VectorInterpolationSchedule
public import QuantitativePaper.VectorSharpMassBounds
public import QuantitativePaper.VectorMeasureTail

@[expose] public section

/-! Genuine joint continuity of finite potentials in the physical
interpolation parameter and the spatial field, including square-root endpoints. -/
noncomputable section
open MeasureTheory Set Filter FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem continuous_vectorTerminalPotential_temperature_field (β : ℝ) (p : Couplings n × ℝ) :
    Continuous (fun z : ℝ × Field n => vectorTerminalPotential n β z.1 p z.2) := by
  simp_rw [vectorTerminalPotential_eq_interpolation_state]
  exact (SpinGlass.AT.contDiff_gtStateLogPartition (fun _ : Configuration n => 0)).continuous.comp
    (by unfold vectorInterpolationState; fun_prop)

theorem vectorColeHopfStep_eq_finiteStateGaussianStep (c m : ℝ) (f : Field n → ℝ) (x : Field n) :
    vectorColeHopfStep c m f x = finiteStateGaussianStep (S := Fin n) (I := Fin n) m
      (Real.sqrt c • ContinuousLinearMap.id ℝ (Field n)) f x := by
  unfold vectorColeHopfStep vectorStepPartition finiteStateGaussianStep OverlapPaper.sourceLogAverage fieldShift
  rw [fieldGaussian_eq_stdGaussian]
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul]

theorem continuous_vectorRecursion_temperature_field (s : RSBScheme k) (β : ℝ)
    (p : Couplings n × ℝ) (j : ℕ) :
    Continuous (fun z : ℝ × Field n => vectorRecursion s β z.1 p j z.2) := by
  induction j with
  | zero => exact continuous_vectorTerminalPotential_temperature_field β p
  | succ j ih =>
    simp_rw [vectorRecursion,vectorColeHopfStep_eq_finiteStateGaussianStep]
    apply continuous_finiteStateGaussianStep_family
      (s.m (k+1-j))
      (fun z : ℝ × Field n => fun x => vectorRecursion s β z.1 p j x)
      (ih.comp ((continuous_fst.fst).prodMk continuous_snd))
      (Real.sqrt (n : ℝ)).toNNReal
      (fun z => vectorRecursion_lipschitz s β z.1 p j)
      (fun z : ℝ × Field n => Real.sqrt ((1-z.1)*(β^2*(s.q (k+2-j)-s.q (k+1-j)))) •
        ContinuousLinearMap.id ℝ (Field n)) (by fun_prop)
      (fun z : ℝ × Field n => z.2) continuous_snd

theorem continuous_vectorDyadicTailPotential_temperature_field (μ : Paper.ParisiMeasure)
    (β : ℝ) (q : Paper.Overlap) (j : ℕ) (p : Couplings n × ℝ) :
    Continuous (fun z : ℝ × Field n => vectorDyadicTailPotential μ β z.1 q j p z.2) := by
  unfold vectorDyadicTailPotential
  simp_rw [vectorTailRecursion_eq_clamped _ β _ q q.property p le_rfl]
  exact continuous_vectorRecursion_temperature_field _ β p _

end QuantitativePaper
