module
public import FourPapersCommon.FiniteGaussianSites
public import OverlapPaper.ReplicaSourceSiteEndpoint
public import OverlapPaper.ReplicaSourceGroupCovariance

@[expose] public section

/-! Literal linear embeddings of site/replica Gaussian coordinates into the
full and constrained replica Hamiltonian fields. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators NNReal
namespace OverlapPaper
open FourPapersCommon SpinGlass.AT
set_option maxHeartbeats 1000000
variable {n d g : ℕ}

 def replicaSiteSpinFieldCLM : FiniteStateField (Fin n×Fin d) →L[ℝ]
    FiniteStateField (ReplicaConfiguration n d) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun σ => ∑ i : Fin n, ∑ l : Fin d, x (i,l)*spin (σ l i))
      map_add' := by intro x y; ext σ; simp [add_mul,Finset.sum_add_distrib]
      map_smul' := by intro c x; ext σ; simp [mul_assoc,Finset.mul_sum] }

 def replicaSiteRestrictedFieldCLM (D : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) :
    FiniteStateField (Fin n×Fin d) →L[ℝ] FiniteStateField (ReplicaSourceState n d D η) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun σ => ∑ i : Fin n, ∑ l : Fin d, x (i,l)*spin (σ.1 l i))
      map_add' := by intro x y; ext σ; simp [add_mul,Finset.sum_add_distrib]
      map_smul' := by intro c x; ext σ; simp [mul_assoc,Finset.mul_sum] }

 def replicaSourceFullPotential (h θ : ℝ) (J : Finset (Fin d)) (σ : ReplicaConfiguration n d) : ℝ :=
  (∑ l : Fin d, h*∑ i : Fin n, spin (σ l i))+θ*∑ i : Fin n, replicaSpinProduct J (fun l => σ l i)

 def replicaSourceSingleSite (h θ : ℝ) (J : Finset (Fin d)) (x : FiniteStateField (Fin d)) : ℝ :=
  replicaSourceTerminal J θ (fun l => h+x l)

 theorem replicaSite_full_terminal_eq (h θ : ℝ) (J : Finset (Fin d))
    (x : FiniteStateField (Fin n×Fin d)) :
    gtStateLogPartition (replicaSourceFullPotential h θ J) (replicaSiteSpinFieldCLM x) =
      finiteGaussianSiteSum (B := Fin n) (replicaSourceSingleSite h θ J) x := by
  have he (σ : ReplicaConfiguration n d) :
      replicaSiteSpinFieldCLM x σ+replicaSourceFullPotential h θ J σ=
        replicaSiteEnergy h θ J (fun i l => x (i,l)) σ := by
    simp only [replicaSiteSpinFieldCLM,replicaSourceFullPotential,replicaSiteEnergy,
      LinearMap.coe_toContinuousLinearMap',LinearMap.coe_mk,AddHom.coe_mk,WithLp.ofLp_toLp,
      Finset.sum_add_distrib,Finset.mul_sum,add_mul]
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin d))) (t := (Finset.univ : Finset (Fin n)))]
    ring
  simp_rw [gtStateLogPartition,gtStatePartition,he]
  exact replicaSiteLogPartition_eq h θ J (fun i l => x (i,l))

 theorem replicaSite_constrained_terminal_le (h θ : ℝ) (J : Finset (Fin d))
    (D : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) (hs : (replicaOverlapShell n d D η).Nonempty)
    (x : FiniteStateField (Fin n×Fin d)) :
    gtStateLogPartition (replicaSourceStatePotential h θ J D η) (replicaSiteRestrictedFieldCLM D η x) ≤
      finiteGaussianSiteSum (B := Fin n) (replicaSourceSingleSite h θ J) x := by
  have he (σ : ReplicaSourceState n d D η) :
      replicaSiteRestrictedFieldCLM D η x σ+replicaSourceStatePotential h θ J D η σ=
        replicaSiteEnergy h θ J (fun i l => x (i,l)) σ.1 := by
    simp only [replicaSiteRestrictedFieldCLM,replicaSourceStatePotential,replicaSiteEnergy,
      LinearMap.coe_toContinuousLinearMap',LinearMap.coe_mk,AddHom.coe_mk,WithLp.ofLp_toLp,
      Finset.sum_add_distrib,Finset.mul_sum,add_mul]
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin d))) (t := (Finset.univ : Finset (Fin n)))]
    ring
  simp_rw [gtStateLogPartition,gtStatePartition,he]
  change Real.log (∑ σ : ↥(replicaOverlapShell n d D η),
    Real.exp (replicaSiteEnergy h θ J (fun i l => x (i,l)) σ.1)) ≤ _
  rw [Finset.sum_coe_sort (replicaOverlapShell n d D η)
    (fun σ => Real.exp (replicaSiteEnergy h θ J (fun i l => x (i,l)) σ))]
  exact constrained_replicaSiteLogPartition_le h θ J D η (fun i l => x (i,l)) hs

 def replicaSingleSiteSpinCLM : FiniteStateField (Fin d) →L[ℝ] FiniteStateField (Configuration d) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun ε => ∑ l : Fin d, x l*spin (ε l))
      map_add' := by intro x y; ext ε; simp [add_mul,Finset.sum_add_distrib]
      map_smul' := by intro c x; ext ε; simp [mul_assoc,Finset.mul_sum] }

 theorem replicaSourceSingleSite_eq_terminal (h θ : ℝ) (J : Finset (Fin d))
    (x : FiniteStateField (Fin d)) :
    replicaSourceSingleSite h θ J x =
      gtStateLogPartition (fun ε : Configuration d => h*∑ l : Fin d, spin (ε l)+θ*replicaSpinProduct J ε)
        (replicaSingleSiteSpinCLM x) := by
  unfold gtStateLogPartition gtStatePartition replicaSourceSingleSite replicaSourceTerminal
  congr 2
  funext ε
  simp only [replicaSingleSiteSpinCLM,LinearMap.coe_toContinuousLinearMap',LinearMap.coe_mk,AddHom.coe_mk,
    WithLp.ofLp_toLp,Finset.sum_add_distrib,Finset.mul_sum,add_mul]
  congr 1
  ring

 theorem replicaSourceSingleSite_lipschitz (h θ : ℝ) (J : Finset (Fin d)) :
    LipschitzWith ‖replicaSingleSiteSpinCLM (d := d)‖₊ (replicaSourceSingleSite h θ J) := by
  let V : Configuration d → ℝ := fun ε => h*∑ l : Fin d, spin (ε l)+θ*replicaSpinProduct J ε
  have hh := (finiteStateGaussianTerminal_lipschitz V).comp (replicaSingleSiteSpinCLM (d := d)).lipschitzWith
  have he : (fun x => gtStateLogPartition V (replicaSingleSiteSpinCLM x))=replicaSourceSingleSite h θ J := by
    funext x
    unfold gtStateLogPartition gtStatePartition replicaSourceSingleSite replicaSourceTerminal
    congr 2
    funext ε
    simp only [replicaSingleSiteSpinCLM,V,LinearMap.coe_toContinuousLinearMap',LinearMap.coe_mk,AddHom.coe_mk,
      WithLp.ofLp_toLp,Finset.sum_add_distrib,Finset.mul_sum,add_mul]
    congr 1
    ring
  rw [←he]
  simpa only [Function.comp_def,one_mul] using hh

 def replicaSiteCopyGaussianCLM (v : ℝ) (groupOf : Fin d → Fin g) :
    FiniteStateGaussianInput (Fin g) →L[ℝ] FiniteStateField (Fin d) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 (fun l => Real.sqrt v*z (groupOf l))
      map_add' := by intro x y; ext l; simp [mul_add]
      map_smul' := by intro c x; ext l; simp; ring }

 @[simp] theorem replicaSiteCopyGaussianCLM_apply (v : ℝ) (groupOf : Fin d → Fin g)
    (z : FiniteStateGaussianInput (Fin g)) (l : Fin d) :
    replicaSiteCopyGaussianCLM v groupOf z l=Real.sqrt v*z (groupOf l) := rfl

 theorem inner_replicaGroupSpinVector_field (groupOf : Fin d → Fin g)
    (l : Fin d) (σ : ReplicaConfiguration n d) (z : EuclideanSpace ℝ (Fin n×Fin g)) :
    inner ℝ (replicaGroupSpinVector groupOf l σ) z=
      ∑ i : Fin n, spin (σ l i)*z (i,groupOf l) := by
  classical
  rw [real_inner_comm,EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct,star_trivial,replicaGroupSpinVector,WithLp.ofLp_toLp,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

 theorem replicaGroupFieldCLM_eq_site_lift (D : Matrix (Fin d) (Fin d) ℝ) (η v : ℝ)
    (groupOf : Fin d → Fin g) :
    replicaGroupFieldCLM (n := n) D η v groupOf =
      (replicaSiteRestrictedFieldCLM D η).comp
        (finiteGaussianSiteLift (B := Fin n) (replicaSiteCopyGaussianCLM v groupOf)) := by
  ext z σ
  rw [replicaGroupFieldCLM_apply]
  simp only [replicaGroupFieldCoordinate,ContinuousLinearMap.sum_apply,smul_apply,
    smul_eq_mul,coe_innerSL_apply,ContinuousLinearMap.comp_apply]
  change (∑ l : Fin d, Real.sqrt v*inner ℝ (replicaGroupSpinVector groupOf l σ.1) z)=
    ∑ i : Fin n, ∑ l : Fin d, Real.sqrt v*z (i,groupOf l)*spin (σ.1 l i)
  simp_rw [inner_replicaGroupSpinVector_field,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro l _
  ring

end OverlapPaper
