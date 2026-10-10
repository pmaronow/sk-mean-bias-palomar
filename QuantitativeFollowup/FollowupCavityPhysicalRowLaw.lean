module
public import QuantitativeFollowup.FollowupCavityIncidentRow
public import QuantitativeFollowup.FollowupCavityRootCharges
public import FourPapersCommon.FiniteCascadeGaussianRowPhysical

@[expose] public section

/-! The actual incident-coupling row of the physical SK cavity genealogy
is the normalized Gaussian terminal-feature law. The dummy zero-mass,
zero-noise root is removed before invoking nonnegative vertex charges. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
open scoped BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem anisotropicRootEnergyMap_scalar_rawKernel_split (D : AnisotropicSpinModel n)
    (e : AnisotropicCouplingIndex n) (H : FiniteStateField (Configuration n)) :
    finiteStateGaussianRawKernel (anisotropicRootEnergyMap D) H =
      finiteStateGaussianRawKernel
        (finiteStateGaussianSumMap (anisotropicRootEnergyMap (anisotropicRemoveCoupling D e))
          (scalarGaussianShift (D.coupling e • anisotropicCouplingFeature e))) H := by
  classical
  apply finiteStateGaussianRawKernel_eq_of_spectral_covariance
  intro σ τ
  rw [finiteStateSpectralCovariance_sumMap, anisotropicRootEnergyMap_covariance_split D e σ τ]
  congr 1
  simp [finiteStateSpectralCovariance, anisotropicCouplingGaussianInput_apply,
    scalarGaussianShift_apply, PiLp.smul_apply, smul_eq_mul]

theorem anisotropicTrimmedTreeRootCoefficient_le (s : RSBScheme k)
    (a : ℝ) (ha : a ≤ s.m 1) (T : FiniteTerminalGenealogy (k+2)) :
    a ≤ finiteCascadeTreeRootCoefficient (anisotropicSchemeMass s) (trimRoot T) := by
  have hc := finiteCascadeTreeRootCoefficient_previous_ge (anisotropicSchemeMass s)
    (anisotropicSchemeMass_nonneg s) (trimRoot T) (by omega)
  have hm : anisotropicSchemeMass s (k+2-1-1) = s.m 1 := by
    simp only [anisotropicSchemeMass]
    congr 1
    omega
  rw [hm] at hc
  exact ha.trans hc

def anisotropicFiniteCouplingRowLaw (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (e : AnisotropicCouplingIndex n)
    (T : FiniteTerminalGenealogy (k+2)) :=
  finiteCascadeTreeGaussianRowLaw (fun _ : Configuration n => 0) (anisotropicCouplingFeature e)
    (anisotropicSchemeMass s)
    (fun j => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s j)) a (D.coupling e^2)
    (trimRoot T) (anisotropicRootEnergyMap (anisotropicRemoveCoupling D e)) 0

theorem anisotropicFiniteCouplingRowLaw_probability (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (ha : a ≤ s.m 1)
    (e : AnisotropicCouplingIndex n) (T : FiniteTerminalGenealogy (k+2)) :
    IsProbabilityMeasure (anisotropicFiniteCouplingRowLaw D s a e T) := by
  apply finiteCascadeTreeGaussianRowLaw_probability _ _ _ (anisotropicSchemeMass_nonneg s)
    (anisotropicSchemeMass_antitone s) (anisotropicSchemeMass_le_one s 0) _ _ _ _
    (anisotropicTrimmedTreeRootCoefficient_le s a ha T) _ _ 1 (by norm_num)
  intro σ
  simp [anisotropicCouplingFeature_apply, abs_mul, Paper.abs_spinSign]

theorem integral_anisotropicFiniteCouplingRowLaw_spins (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (ha : a ≤ s.m 1) (hq : s.q 1 = 0)
    (e : AnisotropicCouplingIndex n) (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration n) (asGenealogy T) → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : 0 ≤ C) (hFb : ∀z,|F z| ≤ C) :
    (∫z,F (trimmedSpinEquiv (S:=Configuration n) T (spins (trimRoot T) z.2.2))
      ∂anisotropicFiniteCouplingRowLaw D s a e T) =
        ∫σ,F σ ∂anisotropicFiniteTreeLaw D s a (asGenealogy T) := by
  let F' : FiniteCascadeGenealogy.Samples (Configuration n) (asGenealogy (trimRoot T)) → ℝ :=
    fun σ => F (trimmedSpinEquiv (S:=Configuration n) T σ)
  have hF' : Measurable F' := hF.comp (trimmedSpinEquiv (S:=Configuration n) T).measurable
  have he := integral_finiteCascadeTreeGaussianRowLaw_physical_spins
    (fun _ : Configuration n => 0) (anisotropicCouplingFeature e)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (anisotropicSchemeMass_antitone s) (anisotropicSchemeMass_le_one s 0)
    (fun j => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s j)) a (D.coupling e)
    (trimRoot T) (anisotropicTrimmedTreeRootCoefficient_le s a ha T)
    (anisotropicRootEnergyMap (anisotropicRemoveCoupling D e)) 0 1 (by norm_num)
    (fun σ => by simp [anisotropicCouplingFeature_apply, abs_mul, Paper.abs_spinSign])
    F' hF' C hC (fun σ => hFb _)
  change (∫z,F (trimmedSpinEquiv (S:=Configuration n) T (spins (trimRoot T) z.2.2))
    ∂anisotropicFiniteCouplingRowLaw D s a e T) = _ at he
  rw [finiteCascadeTreeGaussianJointLaw,
    ← anisotropicRootEnergyMap_scalar_rawKernel_split D e 0] at he
  change _ = ∫z,F (trimmedSpinEquiv (S:=Configuration n) T (spins (trimRoot T) z.2))
    ∂anisotropicTrimmedRecordedTreeLaw D s a T at he
  rw [he, ← anisotropicTrimmedRecordedTreeLaw_spin_marginal D s a hq T]
  have hm : Measurable (fun z : FiniteStateField (Configuration n) ×
      Records (FiniteStateField (Configuration n)) (Configuration n) (trimRoot T) =>
        (trimmedSpinEquiv (S:=Configuration n) T).toEquiv.toFun (spins (trimRoot T) z.2)) :=
    (trimmedSpinEquiv (S:=Configuration n) T).measurable.comp
      ((measurable_spins (trimRoot T)).comp measurable_snd)
  exact (integral_map hm.aemeasurable hF.aestronglyMeasurable).symm

end QuantitativeFollowup
