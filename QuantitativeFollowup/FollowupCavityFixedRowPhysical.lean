module
public import QuantitativeFollowup.FollowupCavityFixedRowDefinitions
public import QuantitativeFollowup.FollowupCavityIncidentRow
public import QuantitativeFollowup.FollowupCavityMixtureGaussian

@[expose] public section

/-! Exact simultaneous incident-row Gaussian realization, with the last
auxiliary-field variance held fixed at its physical zero-row value. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
open SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

def cavityFixedRowVarianceModel (n : ℕ) (beta rho : ℝ) (hbeta : 0<beta)
    (hrho : rho∈Ioc (0:ℝ) 1) (v : ℝ) : AnisotropicSpinModel (n+1) where
  variance := (followupCavitySpinModel n beta rho hbeta hrho 0 ⟨le_rfl,zero_le_one⟩).variance
  variance_pos := (followupCavitySpinModel n beta rho hbeta hrho 0 ⟨le_rfl,zero_le_one⟩).variance_pos
  coupling e := if e.1.1=e.1.2 then 0 else if e.1.2=Fin.last n then Real.sqrt v
    else followupCavityRestCoupling n beta rho

@[simp] theorem cavityFixedRowVarianceModel_zero (beta rho : ℝ) (hbeta : 0<beta)
    (hrho : rho∈Ioc (0:ℝ) 1) :
    cavityFixedRowVarianceModel n beta rho hbeta hrho 0=
      followupCavitySpinModel n beta rho hbeta hrho 0 ⟨le_rfl,zero_le_one⟩ := by
  unfold cavityFixedRowVarianceModel followupCavitySpinModel
  simp only [followupCavityRowCoupling_zero,Real.sqrt_zero]

theorem cavityFixedRowVarianceModel_energyInput (beta rho : ℝ) (hbeta : 0<beta)
    (hrho : rho∈Ioc (0:ℝ) 1) (v : ℝ) (s : RSBScheme k) (j : ℕ) :
    cavityFiniteEnergyInput (cavityFixedRowVarianceModel n beta rho hbeta hrho v) s j=
      cavityFiniteEnergyInput (followupCavitySpinModel n beta rho hbeta hrho 0
        ⟨le_rfl,zero_le_one⟩) s j := by
  ext z sigma
  simp only [cavityFiniteEnergyInput,ContinuousLinearMap.comp_apply,anisotropicSchemeInput_apply,
    anisotropicEnergyMap_apply,anisotropicFieldInjection_apply,anisotropicTerminalLinear_apply,
    anisotropicHamiltonian,PiLp.zero_apply,mul_zero,zero_mul,Finset.sum_const_zero,zero_add]
  rfl

private theorem incident_sum (f : AnisotropicCouplingIndex (n+1)→ℝ) :
    (∑e∈Finset.univ.filter (fun e : AnisotropicCouplingIndex (n+1)=>
      e.1.2=Fin.last n ∧ e.1.1≠e.1.2),f e)=∑i : Fin n,f (followupCavityIncidentIndex i) := by
  classical
  symm
  apply Finset.sum_bij (fun i _=>followupCavityIncidentIndex i)
  · intro i _
    simp [followupCavityIncidentIndex,Fin.castSucc_ne_last]
  · intro i _ j _ hij
    have he:=congrArg (fun e : AnisotropicCouplingIndex (n+1)=>e.1.1.val) hij
    exact Fin.ext he
  · intro e he
    have he':e.1.2=Fin.last n ∧ e.1.1≠e.1.2 := (Finset.mem_filter.mp he).2
    have hl:e.1.1.val<n := by
      have hlt:=e.1.1.isLt
      have hne:e.1.1.val≠n := by
        intro h
        apply he'.2
        rw [he'.1]
        exact Fin.ext h
      omega
    refine ⟨⟨e.1.1.val,hl⟩,Finset.mem_univ _,?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact Fin.ext rfl
    · exact he'.1.symm
  · intro i _
    rfl

theorem cavityFixedRowOffset_single (i : Fin n) (sigma : Configuration (n+1)) :
    cavityFixedRowOffset n (EuclideanSpace.single i 1) sigma=
      anisotropicCouplingFeature (followupCavityIncidentIndex i) sigma := by
  classical
  simp only [cavityFixedRowOffset_apply,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,
    smul_eq_mul,EuclideanSpace.single_apply]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true,one_mul]
    rfl
  · intro j _ hji
    simp [hji]
  · simp

theorem cavityFixedRowVariance_root_covariance (beta rho : ℝ) (hbeta : 0<beta)
    (hrho : rho∈Ioc (0:ℝ) 1) (v : ℝ) (hv : 0≤v)
    (sigma tau : Configuration (n+1)) :
    finiteStateSpectralCovariance
      (anisotropicRootEnergyMap (cavityFixedRowVarianceModel n beta rho hbeta hrho v)) sigma tau=
    finiteStateSpectralCovariance
      (finiteStateGaussianSumMap (Real.sqrt v • cavityFixedRowOffset n)
        (anisotropicRootEnergyMap (followupCavitySpinModel n beta rho hbeta hrho 0
          ⟨le_rfl,zero_le_one⟩))) sigma tau := by
  classical
  rw [finiteStateSpectralCovariance_sumMap]
  simp only [finiteStateSpectralCovariance,ContinuousLinearMap.smul_apply,PiLp.smul_apply,
    smul_eq_mul,cavityFixedRowOffset_single,anisotropicRootEnergyMap_single]
  let P:=fun e : AnisotropicCouplingIndex (n+1)=>e.1.2=Fin.last n ∧ e.1.1≠e.1.2
  have hp (e : AnisotropicCouplingIndex (n+1)) :
      ((cavityFixedRowVarianceModel n beta rho hbeta hrho v).coupling e*
        anisotropicCouplingFeature e sigma)*
      ((cavityFixedRowVarianceModel n beta rho hbeta hrho v).coupling e*
        anisotropicCouplingFeature e tau)=
      (if P e then v*anisotropicCouplingFeature e sigma*anisotropicCouplingFeature e tau else 0)+
      ((followupCavitySpinModel n beta rho hbeta hrho 0 ⟨le_rfl,zero_le_one⟩).coupling e*
        anisotropicCouplingFeature e sigma)*
      ((followupCavitySpinModel n beta rho hbeta hrho 0 ⟨le_rfl,zero_le_one⟩).coupling e*
        anisotropicCouplingFeature e tau) := by
    by_cases he:e.1.1=e.1.2
    · simp [cavityFixedRowVarianceModel,followupCavitySpinModel,he,P]
    · by_cases hl:e.1.2=Fin.last n
      · have hel : e.1.1≠Fin.last n := by simpa only [hl] using he
        simp only [cavityFixedRowVarianceModel,followupCavitySpinModel,hl,hel,ite_false,ite_true,
          followupCavityRowCoupling_zero,mul_zero,zero_mul,add_zero]
        simp only [P,hl,hel,not_false_eq_true,true_and,ite_true]
        calc
          _=(Real.sqrt v)^2*anisotropicCouplingFeature e sigma*anisotropicCouplingFeature e tau := by ring
          _=_ := by rw [Real.sq_sqrt hv]; simp only [if_pos hel]
      · simp [cavityFixedRowVarianceModel,followupCavitySpinModel,he,hl,P]
  simp_rw [hp]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [←Finset.sum_filter,incident_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hs:=Real.sq_sqrt hv
  rw [show Real.sqrt v*anisotropicCouplingFeature (followupCavityIncidentIndex i) sigma*
      (Real.sqrt v*anisotropicCouplingFeature (followupCavityIncidentIndex i) tau)=
      (Real.sqrt v)^2*anisotropicCouplingFeature (followupCavityIncidentIndex i) sigma*
      anisotropicCouplingFeature (followupCavityIncidentIndex i) tau by ring,hs]

theorem cavityFixedRowVariance_recorded_law (beta rho : ℝ) (hbeta : 0<beta)
    (hrho : rho∈Ioc (0:ℝ) 1) (v : ℝ) (hv : 0≤v) (s : RSBScheme k) (a : ℝ) :
    anisotropicFiniteRecordedTreeLaw (cavityFixedRowVarianceModel n beta rho hbeta hrho v)
      s a (observationLinearTree (k+2))=
    finiteCascadeTreeGaussianJointLaw (fun _ : Configuration (n+1)=>0)
      (anisotropicSchemeMass s)
      (cavityFiniteEnergyInput (followupCavitySpinModel n beta rho hbeta hrho 0
        ⟨le_rfl,zero_le_one⟩) s) a (observationLinearTree (k+2))
      (finiteStateGaussianSumMap (Real.sqrt v • cavityFixedRowOffset n)
        (anisotropicRootEnergyMap (followupCavitySpinModel n beta rho hbeta hrho 0
          ⟨le_rfl,zero_le_one⟩))) 0 := by
  have hL:=funext (cavityFixedRowVarianceModel_energyInput (n:=n) beta rho hbeta hrho v s)
  change finiteCascadeTreeGaussianJointLaw _ _
    (cavityFiniteEnergyInput (cavityFixedRowVarianceModel n beta rho hbeta hrho v) s) _ _ _ _=_
  rw [hL]
  unfold finiteCascadeTreeGaussianJointLaw
  rw [finiteStateGaussianRawKernel_eq_of_spectral_covariance _ _
    (cavityFixedRowVariance_root_covariance beta rho hbeta hrho v hv)]

theorem cavityFixedRow_weighted_mixture (beta rho : ℝ) (hbeta : 0<beta)
    (hrho : rho∈Ioc (0:ℝ) 1) (v : ℝ) (hv : 0≤v) (s : RSBScheme k) (a : ℝ)
    (F : FiniteStateField (Configuration (n+1))×
      Records (FiniteStateField (Configuration (n+1))) (Configuration (n+1))
        (observationLinearTree (k+2))→ℝ)
    (hF : Measurable F) (B : ℝ) (hB : 0≤B) (hb : ∀z,‖F z‖≤B) :
    (∫z,F z ∂anisotropicFiniteRecordedTreeLaw
      (cavityFixedRowVarianceModel n beta rho hbeta hrho v) s a (observationLinearTree (k+2)))=
    (∫z,cavityFixedRowNormalizer (followupCavitySpinModel n beta rho hbeta hrho 0
      ⟨le_rfl,zero_le_one⟩) s a (Real.sqrt v • z)*
      (∫r,F r ∂cavityFixedRowLaw (followupCavitySpinModel n beta rho hbeta hrho 0
        ⟨le_rfl,zero_le_one⟩) s a (Real.sqrt v • z)) ∂stdGaussian (Field n))/
    (∫z,cavityFixedRowNormalizer (followupCavitySpinModel n beta rho hbeta hrho 0
      ⟨le_rfl,zero_le_one⟩) s a (Real.sqrt v • z) ∂stdGaussian (Field n)) := by
  rw [cavityFixedRowVariance_recorded_law beta rho hbeta hrho v hv s a]
  simpa only [cavityFixedRowNormalizer,cavityFixedRowLaw,map_smul,
    ContinuousLinearMap.smul_apply,zero_add] using
    cavityGaussianTree_integral_weighted_mixture (fun _ : Configuration (n+1)=>0)
      (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
      (cavityFiniteEnergyInput (followupCavitySpinModel n beta rho hbeta hrho 0
        ⟨le_rfl,zero_le_one⟩) s) a (observationLinearTree (k+2))
      (Real.sqrt v • cavityFixedRowOffset n)
      (anisotropicRootEnergyMap (followupCavitySpinModel n beta rho hbeta hrho 0
        ⟨le_rfl,zero_le_one⟩)) 0 F hF B hB hb

end QuantitativeFollowup
