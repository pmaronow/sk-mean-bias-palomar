module
public import QuantitativeFollowup.FollowupCavityFixedRowPhysical
public import QuantitativeFollowup.FollowupCavityCppZeroResponseLastVariance

@[expose] public section

/-! The literal two-clock model varies only the incident-row variance and
last auxiliary variance. Every rest coefficient is unchanged. Its physical
curve is exactly the source's original u model, with no reparameterization. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
open SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

def cavityFixedRowTwoClockModel (n : ℕ) (beta rho : ℝ) (hbeta : 0<beta)
    (hrho : rho∈Ioc (0:ℝ) 1) (b : ℝ) (hb : 0<b) (v : ℝ) : AnisotropicSpinModel (n+1) where
  variance := (cavityLastVarianceModel n beta rho hbeta hrho b hb).variance
  variance_pos := (cavityLastVarianceModel n beta rho hbeta hrho b hb).variance_pos
  coupling := (cavityFixedRowVarianceModel n beta rho hbeta hrho v).coupling

@[simp] theorem cavityFixedRowTwoClockModel_energyInput (beta rho : ℝ) (hbeta : 0<beta)
    (hrho : rho∈Ioc (0:ℝ) 1) (b : ℝ) (hb : 0<b) (v : ℝ) (s : RSBScheme k) (j : ℕ) :
    cavityFiniteEnergyInput (cavityFixedRowTwoClockModel n beta rho hbeta hrho b hb v) s j=
      cavityFiniteEnergyInput (cavityLastVarianceModel n beta rho hbeta hrho b hb) s j := by
  ext z sigma
  simp only [cavityFiniteEnergyInput,ContinuousLinearMap.comp_apply,anisotropicSchemeInput_apply,
    anisotropicEnergyMap_apply,anisotropicFieldInjection_apply,anisotropicTerminalLinear_apply,
    anisotropicHamiltonian,PiLp.zero_apply,mul_zero,zero_mul,Finset.sum_const_zero,zero_add]
  rfl

@[simp] theorem cavityFixedRowTwoClockModel_root (beta rho : ℝ) (hbeta : 0<beta)
    (hrho : rho∈Ioc (0:ℝ) 1) (b : ℝ) (hb : 0<b) (v : ℝ) :
    anisotropicRootEnergyMap (cavityFixedRowTwoClockModel n beta rho hbeta hrho b hb v)=
      anisotropicRootEnergyMap (cavityFixedRowVarianceModel n beta rho hbeta hrho v) := rfl

@[simp] theorem cavityLastVarianceModel_root (beta rho : ℝ) (hbeta : 0<beta)
    (hrho : rho∈Ioc (0:ℝ) 1) (b : ℝ) (hb : 0<b) :
    anisotropicRootEnergyMap (cavityLastVarianceModel n beta rho hbeta hrho b hb)=
      anisotropicRootEnergyMap (followupCavitySpinModel n beta rho hbeta hrho 0
        ⟨le_rfl,zero_le_one⟩) := rfl

theorem cavityFixedRowTwoClockModel_physical (beta rho : ℝ) (hbeta : 0<beta)
    (hrho : rho∈Ioc (0:ℝ) 1) (u : ℝ) (hu : u∈Icc (0:ℝ) 1)
    (hb : 0<followupCavityB n beta rho u) :
    cavityFixedRowTwoClockModel n beta rho hbeta hrho (followupCavityB n beta rho u) hb
      (followupCavityAlpha n beta rho*u/(n:ℝ))=
      followupCavitySpinModel n beta rho hbeta hrho u hu := by
  unfold cavityFixedRowTwoClockModel cavityLastVarianceModel cavityFixedRowVarianceModel followupCavitySpinModel
  simp only [followupCavityRowCoupling]
  congr 1
  funext i
  split_ifs <;> rfl

theorem cavityFixedRowTwoClock_recorded_law (beta rho : ℝ) (hbeta : 0<beta)
    (hrho : rho∈Ioc (0:ℝ) 1) (b : ℝ) (hb : 0<b) (v : ℝ) (hv : 0≤v)
    (s : RSBScheme k) (a : ℝ) :
    anisotropicFiniteRecordedTreeLaw (cavityFixedRowTwoClockModel n beta rho hbeta hrho b hb v)
      s a (observationLinearTree (k+2))=
      finiteCascadeTreeGaussianJointLaw (fun _ : Configuration (n+1)=>0) (anisotropicSchemeMass s)
        (cavityFiniteEnergyInput (cavityLastVarianceModel n beta rho hbeta hrho b hb) s) a
        (observationLinearTree (k+2))
        (finiteStateGaussianSumMap (Real.sqrt v • cavityFixedRowOffset n)
          (anisotropicRootEnergyMap (cavityLastVarianceModel n beta rho hbeta hrho b hb))) 0 := by
  change finiteCascadeTreeGaussianJointLaw _ _
    (cavityFiniteEnergyInput (cavityFixedRowTwoClockModel n beta rho hbeta hrho b hb v) s) _ _ _ _=_
  have hi : cavityFiniteEnergyInput (cavityFixedRowTwoClockModel n beta rho hbeta hrho b hb v) s=
      cavityFiniteEnergyInput (cavityLastVarianceModel n beta rho hbeta hrho b hb) s :=
    funext fun j=>cavityFixedRowTwoClockModel_energyInput beta rho hbeta hrho b hb v s j
  rw [hi]
  unfold finiteCascadeTreeGaussianJointLaw
  rw [finiteStateGaussianRawKernel_eq_of_spectral_covariance _ _ (by
    intro sigma tau
    simpa only [cavityFixedRowTwoClockModel_root,cavityLastVarianceModel_root] using
      cavityFixedRowVariance_root_covariance beta rho hbeta hrho v hv sigma tau)]
  rw [cavityLastVarianceModel_root]

theorem cavityFixedRowTwoClock_weighted_mixture (beta rho : ℝ) (hbeta : 0<beta)
    (hrho : rho∈Ioc (0:ℝ) 1) (b : ℝ) (hb : 0<b) (v : ℝ) (hv : 0≤v)
    (s : RSBScheme k) (a : ℝ)
    (F : FiniteStateField (Configuration (n+1))×Records (FiniteStateField (Configuration (n+1)))
      (Configuration (n+1)) (observationLinearTree (k+2))→ℝ)
    (hF : Measurable F) (B : ℝ) (hB : 0≤B) (hbound : ∀z,‖F z‖≤B) :
    (∫z,F z∂anisotropicFiniteRecordedTreeLaw
      (cavityFixedRowTwoClockModel n beta rho hbeta hrho b hb v) s a (observationLinearTree (k+2)))=
      (∫theta : Field n,cavityFixedRowNormalizer (cavityLastVarianceModel n beta rho hbeta hrho b hb) s a
          (Real.sqrt v • theta)*
        (∫z,F z∂cavityFixedRowLaw (cavityLastVarianceModel n beta rho hbeta hrho b hb) s a
          (Real.sqrt v • theta)) ∂stdGaussian (Field n))/
      (∫theta : Field n,cavityFixedRowNormalizer (cavityLastVarianceModel n beta rho hbeta hrho b hb) s a
        (Real.sqrt v • theta)∂stdGaussian (Field n)) := by
  rw [cavityFixedRowTwoClock_recorded_law beta rho hbeta hrho b hb v hv s a]
  simpa only [zero_add,ContinuousLinearMap.smul_apply,map_smul,cavityFixedRowLaw,cavityFixedRowNormalizer] using
    cavityGaussianTree_integral_weighted_mixture (fun _ : Configuration (n+1)=>0)
      (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
      (cavityFiniteEnergyInput (cavityLastVarianceModel n beta rho hbeta hrho b hb) s) a
      (observationLinearTree (k+2))
      (Real.sqrt v • cavityFixedRowOffset n)
      (anisotropicRootEnergyMap (cavityLastVarianceModel n beta rho hbeta hrho b hb)) 0 F hF B hB hbound

end QuantitativeFollowup
