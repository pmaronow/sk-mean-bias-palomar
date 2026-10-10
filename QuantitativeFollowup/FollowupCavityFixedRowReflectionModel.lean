module
public import QuantitativeFollowup.FollowupCavityFixedRowReflectionRecords
public import QuantitativeFollowup.FollowupCavityFixedRowDefinitions
public import QuantitativeFollowup.FollowupCavityDecouplingHamiltonian
public import QuantitativePaper.VectorSiteSymmetry

@[expose] public section

/-! Literal last-spin reflection for the deterministic cavity row. The
remaining Gaussian field coordinates are reflected by a true orthogonal
map; the u=0 disorder field is unchanged and the row becomes its negative. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open FourPapersCommon QuantitativePaper SpinGlass.Targets
open scoped BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

def cavityLastEnergyReflection (n : ℕ) :
    FiniteStateField (Configuration (n+1)) ≃ₗᵢ[ℝ] FiniteStateField (Configuration (n+1)) :=
  cavityStatePermutation (flipSpinEquiv (Fin.last n))

@[simp] theorem cavityLastEnergyReflection_apply (H : FiniteStateField (Configuration (n+1)))
    (sigma : Configuration (n+1)) :
    cavityLastEnergyReflection n H sigma = H (flipSpin (Fin.last n) sigma) := rfl

theorem cavityLastEnergyReflection_input (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (j : ℕ) (z : QuantitativePaper.Field (n+1)) :
    cavityLastEnergyReflection n (cavityFiniteEnergyInput D s j z) =
      cavityFiniteEnergyInput D s j (siteFieldReflection (Fin.last n) z) := by
  have hn : anisotropicNoiseMap D (siteFieldReflection (Fin.last n) z) =
      siteFieldReflection (Fin.last n) (anisotropicNoiseMap D z) := by
    ext i
    simp only [anisotropicNoiseMap_apply, siteFieldReflection_apply]
    ring
  ext sigma
  simp only [cavityLastEnergyReflection_apply, cavityFiniteEnergyInput,
    ContinuousLinearMap.comp_apply, anisotropicSchemeInput_apply,
    anisotropicEnergyMap_field, hn, ←map_smul, fieldDot_site_reflection]

theorem cavityLastEnergyReflection_offset (theta : QuantitativePaper.Field n) :
    cavityLastEnergyReflection n (cavityFixedRowOffset n theta) =
      cavityFixedRowOffset n (-theta) := by
  ext sigma
  simp only [cavityLastEnergyReflection_apply, cavityFixedRowOffset_apply,
    WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, PiLp.neg_apply]
  apply Finset.sum_congr rfl
  intro i _
  change theta i * (Paper.spinSign (flipSpin (Fin.last n) sigma i.castSucc) *
      Paper.spinSign (flipSpin (Fin.last n) sigma (Fin.last n))) =
    -theta i * (Paper.spinSign (sigma i.castSucc) * Paper.spinSign (sigma (Fin.last n)))
  rw [spinSign_flipSpin, spinSign_flipSpin]
  simp only [siteSign, Fin.castSucc_ne_last, ite_false, ite_true]
  ring

theorem cavityLastEnergyReflection_root (beta rho : ℝ) (hbeta : 0 < beta)
    (hrho : rho ∈ Ioc 0 1) (g : AnisotropicDisorder (n+1)) :
    cavityLastEnergyReflection n
        (anisotropicRootEnergyMap (followupCavitySpinModel n beta rho hbeta hrho 0
          ⟨le_rfl, zero_le_one⟩) g) =
      anisotropicRootEnergyMap (followupCavitySpinModel n beta rho hbeta hrho 0
          ⟨le_rfl, zero_le_one⟩) g := by
  ext sigma
  simp only [cavityLastEnergyReflection_apply, anisotropicRootEnergyMap,
    ContinuousLinearMap.comp_apply, anisotropicDisorderInjection_apply,
    anisotropicEnergyMap_apply, anisotropicTerminalLinear_apply]
  have hs : cavityRestConfiguration (flipSpin (Fin.last n) sigma) =
      cavityRestConfiguration sigma := by
    funext i
    exact flipSpin_away (Fin.last n) i.castSucc sigma (Fin.castSucc_ne_last i)
  rw [followupCavityHamiltonian_zero, followupCavityHamiltonian_zero, hs]
  simp only [PiLp.zero_apply, zero_mul, add_zero]

theorem cavityFixedRowNormalizer_reflection (beta rho : ℝ) (hbeta : 0 < beta)
    (hrho : rho ∈ Ioc 0 1) (s : RSBScheme k) (a : ℝ) (theta : QuantitativePaper.Field n) :
    cavityFixedRowNormalizer (followupCavitySpinModel n beta rho hbeta hrho 0
        ⟨le_rfl, zero_le_one⟩) s a (-theta) =
      cavityFixedRowNormalizer (followupCavitySpinModel n beta rho hbeta hrho 0
        ⟨le_rfl, zero_le_one⟩) s a theta := by
  let D := followupCavitySpinModel n beta rho hbeta hrho 0 ⟨le_rfl, zero_le_one⟩
  unfold cavityFixedRowNormalizer
  rw [←cavityLastEnergyReflection_offset theta]
  exact cavityGaussianNormalizer_statePermutation (flipSpinEquiv (Fin.last n))
    (fun _ => 0) (fun _ => rfl) (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (cavityFiniteEnergyInput D s) (fun _ => siteFieldReflection (Fin.last n))
    (cavityLastEnergyReflection_input D s) (anisotropicRootEnergyMap D)
    (LinearIsometryEquiv.refl ℝ _) (fun g => cavityLastEnergyReflection_root beta rho hbeta hrho g)
    a (k+2) (cavityFixedRowOffset n theta)

theorem cavityFixedRowLaw_reflection (beta rho : ℝ) (hbeta : 0 < beta)
    (hrho : rho ∈ Ioc 0 1) (s : RSBScheme k) (a : ℝ) (theta : QuantitativePaper.Field n) :
    (cavityFixedRowLaw (followupCavitySpinModel n beta rho hbeta hrho 0
        ⟨le_rfl, zero_le_one⟩) s a theta).map
      (Prod.map (cavityLastEnergyReflection n)
        (cavityPermuteRecords (flipSpinEquiv (Fin.last n)) (observationLinearTree (k+2)))) =
      cavityFixedRowLaw (followupCavitySpinModel n beta rho hbeta hrho 0
        ⟨le_rfl, zero_le_one⟩) s a (-theta) := by
  let D := followupCavitySpinModel n beta rho hbeta hrho 0 ⟨le_rfl, zero_le_one⟩
  unfold cavityFixedRowLaw
  rw [←cavityLastEnergyReflection_offset theta]
  exact cavityGaussianJointLaw_statePermutation (flipSpinEquiv (Fin.last n))
    (fun _ => 0) (fun _ => rfl) (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (cavityFiniteEnergyInput D s) (fun _ => siteFieldReflection (Fin.last n))
    (cavityLastEnergyReflection_input D s) (anisotropicRootEnergyMap D)
    (LinearIsometryEquiv.refl ℝ _) (fun g => cavityLastEnergyReflection_root beta rho hbeta hrho g)
    a (observationLinearTree (k+2)) (cavityFixedRowOffset n theta)

end QuantitativeFollowup
