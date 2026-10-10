module
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
public import Mathlib.MeasureTheory.VectorMeasure.Operations
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic

@[expose] public section

/-! Ordinary local density domination from an actual signed-density
identity. No Radon--Nikodym bound is included in the conclusion's inputs. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem restrict_le_of_signed_density (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (I : Set ℝ) (hI : MeasurableSet I)
    (hvol : volume I ≠ ⊤) (g : ℝ → ℝ) (hg : Integrable g volume)
    (tau C K : ℝ) (htau : 0 ≤ tau) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hbound : ∀x∈I, -K ≤ g x)
    (hidentity : ν.toSignedMeasure=μ.toSignedMeasure-tau • volume.withDensityᵥ g)
    (hdom : μ.restrict I ≤ ENNReal.ofReal C • volume.restrict I) :
    ν.restrict I ≤ ENNReal.ofReal (C+tau*K) • volume.restrict I := by
  apply Measure.le_iff.mpr
  intro S hS
  let A := S∩I
  have hA : MeasurableSet A := hS.inter hI
  have hAfin : volume A ≠ ⊤ := (lt_of_le_of_lt (measure_mono inter_subset_right)
    (lt_top_iff_ne_top.mpr hvol)).ne
  let : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.mpr hAfin
  have hEq := congrArg (fun v : SignedMeasure ℝ => v A) hidentity
  rw [Measure.toSignedMeasure_apply_measurable hA,_root_.sub_apply,_root_.smul_apply,
    Measure.toSignedMeasure_apply_measurable hA,withDensityᵥ_apply hg hA,smul_eq_mul] at hEq
  have hOld := hdom S
  simp only [Measure.restrict_apply hS,Measure.smul_apply,smul_eq_mul] at hOld ⊢
  have hOldReal : (μ A).toReal ≤ C*(volume A).toReal := by
    have hh := ENNReal.toReal_mono (by finiteness : ENNReal.ofReal C*volume A ≠ ⊤) hOld
    simpa only [A,ENNReal.toReal_mul,ENNReal.toReal_ofReal hC] using hh
  have hLow := setIntegral_mono_on (integrable_const (-K)) hg.integrableOn hA
    (fun x hx => hbound x hx.2)
  rw [setIntegral_const,smul_eq_mul] at hLow
  have hreal : (ν A).toReal ≤ (C+tau*K)*(volume A).toReal := by
    change (ν A).toReal=(μ A).toReal-tau*(∫x in A,g x) at hEq
    change (volume A).toReal*(-K) ≤ ∫x in A,g x at hLow
    nlinarith [mul_nonneg htau (sub_nonneg.mpr hLow)]
  apply (ENNReal.toReal_le_toReal (measure_ne_top ν A)
    (by finiteness : ENNReal.ofReal (C+tau*K)*volume A ≠ ⊤)).mp
  simpa only [A,ENNReal.toReal_mul,ENNReal.toReal_ofReal (add_nonneg hC (mul_nonneg htau hK))] using hreal

end QuantitativeFollowup
