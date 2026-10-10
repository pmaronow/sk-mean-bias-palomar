module
public import QuantitativeFollowup.FollowupCavityRecordedDensity
public import FourPapersCommon.FiniteStateGaussianConvolutionCovariance

@[expose] public section

/-! Splitting an actual independent incident coupling from the SK disorder.
The removed coordinate changes the root Gaussian field, and leaves every
auxiliary-field increment unchanged. The law identity uses the actual
Gaussian spectral covariance, including zero coupling scales. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 256
set_option backward.isDefEq.respectTransparency false

def anisotropicRemoveCoupling (D : AnisotropicSpinModel n)
    (e : AnisotropicCouplingIndex n) : AnisotropicSpinModel n where
  variance := D.variance
  variance_pos := D.variance_pos
  coupling f := if f = e then 0 else D.coupling f

def anisotropicCouplingFeature (e : AnisotropicCouplingIndex n) :
    FiniteStateField (Configuration n) :=
  WithLp.toLp 2 (fun σ => Paper.spinSign (σ e.1.1) * Paper.spinSign (σ e.1.2))

@[simp] theorem anisotropicCouplingFeature_apply (e : AnisotropicCouplingIndex n)
    (σ : Configuration n) :
    anisotropicCouplingFeature e σ = Paper.spinSign (σ e.1.1) * Paper.spinSign (σ e.1.2) := rfl

def anisotropicCouplingGaussianInput (D : AnisotropicSpinModel n)
    (e : AnisotropicCouplingIndex n) :
    FiniteStateGaussianInput Unit →L[ℝ] FiniteStateField (Configuration n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => (D.coupling e * z ()) • anisotropicCouplingFeature e
      map_add' := by intro z w; simp only [PiLp.add_apply, mul_add, add_smul]
      map_smul' := by
        intro c z
        simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, smul_smul]
        congr 1
        ring }

@[simp] theorem anisotropicCouplingGaussianInput_apply (D : AnisotropicSpinModel n)
    (e : AnisotropicCouplingIndex n) (z : FiniteStateGaussianInput Unit)
    (σ : Configuration n) :
    anisotropicCouplingGaussianInput D e z σ =
      D.coupling e * z () * anisotropicCouplingFeature e σ := by
  change (D.coupling e * z ()) * anisotropicCouplingFeature e σ = _
  rfl

theorem anisotropicRootEnergyMap_apply (D : AnisotropicSpinModel n)
    (ω : AnisotropicDisorder n) (σ : Configuration n) :
    anisotropicRootEnergyMap D ω σ =
      ∑ e : AnisotropicCouplingIndex n, D.coupling e * ω e * anisotropicCouplingFeature e σ := by
  rw [anisotropicRootEnergyMap, ContinuousLinearMap.comp_apply,
    anisotropicDisorderInjection_apply, anisotropicEnergyMap_apply,
    anisotropicTerminalLinear_apply]
  simp only [anisotropicHamiltonian, fieldDot, PiLp.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero, anisotropicCouplingFeature_apply]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem anisotropicRootEnergyMap_single (D : AnisotropicSpinModel n)
    (e : AnisotropicCouplingIndex n) (σ : Configuration n) :
    anisotropicRootEnergyMap D (EuclideanSpace.single e 1) σ =
      D.coupling e * anisotropicCouplingFeature e σ := by
  classical
  simp [anisotropicRootEnergyMap_apply]

theorem anisotropicRootEnergyMap_remove (D : AnisotropicSpinModel n)
    (e : AnisotropicCouplingIndex n) (ω : AnisotropicDisorder n) :
    anisotropicRootEnergyMap D ω =
      anisotropicRootEnergyMap (anisotropicRemoveCoupling D e) ω +
        (D.coupling e * ω e) • anisotropicCouplingFeature e := by
  classical
  ext σ
  simp only [anisotropicRootEnergyMap_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ e),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ e)]
  simp only [anisotropicRemoveCoupling, ite_true, zero_mul, add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro f hf
  simp [Finset.ne_of_mem_erase hf]

theorem anisotropicEnergyInputs_removeCoupling (D : AnisotropicSpinModel n)
    (e : AnisotropicCouplingIndex n) (s : RSBScheme k) (j : ℕ) :
    (anisotropicEnergyMap (anisotropicRemoveCoupling D e)).comp
        (anisotropicSchemeInput (anisotropicRemoveCoupling D e) s j) =
      (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s j) := by
  ext z σ
  simp only [ContinuousLinearMap.comp_apply, anisotropicSchemeInput_apply,
    anisotropicEnergyMap_apply, anisotropicFieldInjection_apply,
    anisotropicTerminalLinear_apply, anisotropicHamiltonian, PiLp.zero_apply,
    mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
  rfl

theorem anisotropicRootEnergyMap_covariance_split (D : AnisotropicSpinModel n)
    (e : AnisotropicCouplingIndex n) (σ τ : Configuration n) :
    finiteStateSpectralCovariance (anisotropicRootEnergyMap D) σ τ =
      finiteStateSpectralCovariance (anisotropicRootEnergyMap (anisotropicRemoveCoupling D e)) σ τ +
        finiteStateSpectralCovariance (anisotropicCouplingGaussianInput D e) σ τ := by
  classical
  simp only [finiteStateSpectralCovariance, anisotropicRootEnergyMap_single]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ e),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ e)]
  have hsum : (∑ f ∈ Finset.univ.erase e,
      (D.coupling f * anisotropicCouplingFeature f σ) *
        (D.coupling f * anisotropicCouplingFeature f τ)) =
      ∑ f ∈ Finset.univ.erase e,
        ((anisotropicRemoveCoupling D e).coupling f * anisotropicCouplingFeature f σ) *
          ((anisotropicRemoveCoupling D e).coupling f * anisotropicCouplingFeature f τ) := by
    apply Finset.sum_congr rfl
    intro f hf
    simp [anisotropicRemoveCoupling, Finset.ne_of_mem_erase hf]
  rw [hsum]
  simp [anisotropicRemoveCoupling, anisotropicCouplingGaussianInput_apply]

theorem anisotropicRootEnergyMap_rawKernel_split (D : AnisotropicSpinModel n)
    (e : AnisotropicCouplingIndex n) (H : FiniteStateField (Configuration n)) :
    finiteStateGaussianRawKernel (anisotropicRootEnergyMap D) H =
      finiteStateGaussianRawKernel
        (finiteStateGaussianSumMap (anisotropicRootEnergyMap (anisotropicRemoveCoupling D e))
          (anisotropicCouplingGaussianInput D e)) H := by
  apply finiteStateGaussianRawKernel_eq_of_spectral_covariance
  intro σ τ
  rw [finiteStateSpectralCovariance_sumMap]
  exact anisotropicRootEnergyMap_covariance_split D e σ τ

def followupCavityIncidentIndex (i : Fin n) : AnisotropicCouplingIndex (n+1) :=
  ⟨(i.castSucc, Fin.last n), by exact Nat.le_of_lt i.isLt⟩

theorem followupCavityIncidentIndex_coupling (β ρ : ℝ) (hβ : 0 < β)
    (hρ : ρ ∈ Ioc 0 1) (u : ℝ) (hu : u ∈ Icc 0 1) (i : Fin n) :
    (followupCavitySpinModel n β ρ hβ hρ u hu).coupling (followupCavityIncidentIndex i) =
      followupCavityRowCoupling n β ρ u := by
  simp [followupCavitySpinModel, followupCavityIncidentIndex, Fin.castSucc_ne_last]

theorem followupCavityIncidentIndex_variance (β ρ : ℝ) (hβ : 0 < β)
    (hρ : ρ ∈ Ioc 0 1) (u : ℝ) (hu : u ∈ Icc 0 1) (i : Fin n) :
    (followupCavitySpinModel n β ρ hβ hρ u hu).coupling (followupCavityIncidentIndex i) ^ 2 =
      followupCavityAlpha n β ρ * u / (n:ℝ) := by
  rw [followupCavityIncidentIndex_coupling]
  exact followupCavityRowCoupling_square n β ρ u hρ.2 hu.1

end QuantitativeFollowup
