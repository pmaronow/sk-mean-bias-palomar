module
public import QuantitativeFollowup.FollowupCavityPhysicalRowLaw
public import FourPapersCommon.FiniteCascadeGaussianRowRecordLaw

@[expose] public section

/-! The selected physical Gaussian coupling row retains the entire actual
trimmed field/spin history, so conditional marks use the physical vertices. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem anisotropicFiniteCouplingRowLaw_physical_records_map (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (ha : a ≤ s.m 1)
    (e : AnisotropicCouplingIndex n) (T : FiniteTerminalGenealogy (k+2)) :
    (anisotropicFiniteCouplingRowLaw D s a e T).map
      (finiteCascadeGaussianRowPhysicalRecords (anisotropicCouplingFeature e) (trimRoot T)) =
      anisotropicTrimmedRecordedTreeLaw D s a T := by
  have he := finiteCascadeTreeGaussianRowLaw_physical_records_map
    (fun _ : Configuration n => 0) (anisotropicCouplingFeature e)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (anisotropicSchemeMass_antitone s) (anisotropicSchemeMass_le_one s 0)
    (fun j => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s j)) a (D.coupling e)
    (trimRoot T) (anisotropicTrimmedTreeRootCoefficient_le s a ha T)
    (anisotropicRootEnergyMap (anisotropicRemoveCoupling D e)) 0 1 (by norm_num)
    (fun σ => by simp [anisotropicCouplingFeature_apply,abs_mul,Paper.abs_spinSign])
  change (anisotropicFiniteCouplingRowLaw D s a e T).map
      (finiteCascadeGaussianRowPhysicalRecords (anisotropicCouplingFeature e) (trimRoot T)) = _ at he
  rw [finiteCascadeTreeGaussianJointLaw,
    ← anisotropicRootEnergyMap_scalar_rawKernel_split D e 0] at he
  exact he

end QuantitativeFollowup
