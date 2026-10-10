module
public import QuantitativeFollowup.FollowupCavityInterpolationScore

@[expose] public section

/-! The two-clock Gaussian sample maps to the actual retained physical
record. Coupling rescaling changes its independent initial disorder and
keeps all future path coordinates intact. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

theorem cavityPathFixedRecord_scaleRootCouplings (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (u : ℝ) (s : RSBScheme k) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (σ : TerminalSpins (Configuration n) T) (z : CavityPathGaussianSpace T n) :
    cavityPathFixedRecord (anisotropicScaleRootCouplings D p u) s i T σ z=
      cavityPathFixedRecord D s i T σ (gaussianSelectedScale (cavityRootCouplingMask p T) u z) := by
  have hL : cavityFiniteEnergyInput
      (anisotropicReplaceVariance (anisotropicScaleRootCouplings D p u) i 1) s=
      cavityFiniteEnergyInput (anisotropicReplaceVariance D i 1) s := by
    funext q
    exact cavityFiniteEnergyInput_scaleRootCouplings_variance D p u i 1 s q
  unfold cavityPathFixedRecord
  rw [hL,anisotropicRootEnergyMap_scaleRootCouplings]
  unfold finiteCascadeTreeReferenceRootFlatRecord
  rw [finiteGaussianLeft_cavityRootScale,finiteGaussianRight_cavityRootScale]
  rfl

def cavityInterpolationPhysicalRecord (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (s : RSBScheme k) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (u b : ℝ) :=
  cavityPathPhysicalRecord (anisotropicScaleRootCouplings D p u) s i T b

theorem cavityInterpolationPhysicalRecord_eq_fixed_record (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (s : RSBScheme k) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (u b : ℝ) (hb : 0<b) (z : CavityPathGaussianSpace T n×TerminalSpins (Configuration n) T) :
    cavityInterpolationPhysicalRecord D p s i T u b z=
      cavityPathFixedRecord D s i T z.2 (cavityInterpolationGaussianScale p i T u b z.1) := by
  rw [show cavityInterpolationPhysicalRecord D p s i T u b z=
    cavityPathPhysicalRecord (anisotropicScaleRootCouplings D p u) s i T b z from rfl,
      cavityPathPhysicalRecord_eq_fixed_record _ s i T b hb z,cavityPathFixedRecord_scaleRootCouplings]
  rfl

theorem measurable_cavityInterpolationPhysicalRecord (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (s : RSBScheme k) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (u b : ℝ) :
    Measurable (cavityInterpolationPhysicalRecord D p s i T u b) :=
  measurable_finiteCascadeTreeReferenceRootFlatRecord _ _ _ _

theorem measurable_cavityInterpolationRecordScore (D : AnisotropicSpinModel n)
    (p : AnisotropicCouplingIndex n→Bool) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hj : j≤k+2) (alpha b : ℝ) (hb : 0<b) :
    Measurable (cavityInterpolationRecordScore D p s a i T alpha b) := by
  unfold cavityInterpolationRecordScore
  apply Measurable.sub
  · apply measurable_const.mul
    apply Finset.measurable_sum
    intro e _
    by_cases he:p e=true
    · simp only [ite_eq_left he]
      exact measurable_const.mul (measurable_finiteCascadeIntrinsicRowCurvature _ _ _
        (anisotropicSchemeMass_nonneg s) _ _ _)
    · simp only [ite_eq_right he]
      exact measurable_const
  · exact measurable_const.mul (measurable_cavityPathRecordScore D s a i T hj b hb)

end QuantitativeFollowup
