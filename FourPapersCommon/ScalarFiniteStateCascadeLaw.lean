module
public import FourPapersCommon.ScalarFiniteStateCascade
public import FourPapersCommon.KernelExpectationIntertwining
public import OverlapPaper.ReplicaSourceSiteStepLaw
public import OverlapPaper.ReplicaSourceGroupedMoments

@[expose] public section

/-! Actual scalar normalized-kernel laws for the one-spin Gaussian cascade.
The parent-field transition is the selected Parisi scalar transition, including
zero mass and variance. Arbitrary measurable parent tests are transported. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Real
open scoped BigOperators
namespace FourPapersCommon
open OverlapPaper SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 1600000

def scalarSiteSchemeInput {k : ℕ} (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    FiniteStateGaussianInput (Fin 1)→L[ℝ]FiniteStateField (Fin 1) :=
  replicaSiteCopyGaussianCLM (scalarSchemeVariance s β j) (id : Fin 1→Fin 1)

def scalarSiteSchemeCascade {k : ℕ} (s : RSBScheme k) (β h : ℝ) (j : ℕ) :=
  finiteStateGaussianCascade (scalarSchemeMass s) (scalarSiteSchemeInput s β)
    (replicaSourceSingleSite h 0 (∅ : Finset (Fin 1))) j

def scalarSiteSchemeKernel {k : ℕ} (s : RSBScheme k) (β h : ℝ) (j : ℕ) :=
  finiteStateGaussianCascadeKernel (scalarSchemeMass s) (scalarSiteSchemeInput s β)
    (replicaSourceSingleSite h 0 (∅ : Finset (Fin 1))) j

def scalarSiteAbsolute (h : ℝ) (H : FiniteStateField (Fin 1)) : ℝ := h+H 0

theorem measurable_scalarSiteAbsolute (h : ℝ) : Measurable (scalarSiteAbsolute h) := by
  unfold scalarSiteAbsolute
  fun_prop

theorem scalarSiteSchemeCascade_lipschitz {k : ℕ} (s : RSBScheme k) (β h : ℝ) (j : ℕ) :
    LipschitzWith ‖replicaSingleSiteSpinCLM (d:=1)‖₊ (scalarSiteSchemeCascade s β h j) :=
  finiteStateGaussianCascade_lipschitz _ (replicaSourceSingleSite_lipschitz h 0 ∅)
    _ (scalarSchemeMass_nonneg s) _ j

theorem scalarSiteSchemeCascade_eq_potential {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : 0<β) (h : ℝ) (j : ℕ) (hj : j≤k+2)
    (H : FiniteStateField (Fin 1)) :
    scalarSiteSchemeCascade s β h j H=Real.log 2+
      Paper.parisiPotential β (Paper.parisiSchemeMeasure s) (s.q (k+2-j),scalarSiteAbsolute h H) := by
  have hF : (fun y=>gtStateLogPartition (scalarSpinPotential h) (replicaSingleSiteSpinCLM y))=
      replicaSourceSingleSite h 0 (∅ : Finset (Fin 1)) := by
    funext y
    rw [replicaSourceSingleSite_eq_terminal]
    simp only [zero_mul,add_zero]
    rfl
  have he:=finiteStateGaussianCascade_comp_linear (replicaSingleSiteSpinCLM (d:=1))
    (scalarSiteSchemeInput s β) (scalarSchemeMass s) (gtStateLogPartition (scalarSpinPotential h)) j H
  rw [hF] at he
  change finiteStateGaussianTerminalCascade (scalarSpinPotential h) (scalarSchemeMass s)
    (scalarSchemeSpinInput s β) j (replicaSingleSiteSpinCLM H)=scalarSiteSchemeCascade s β h j H at he
  rw [←he]
  exact scalarGaussianTerminalCascade_scheme s β hβ h j hj H

/-- Equality of actual pushed probability laws, not merely an identity for
one chosen observable. -/
theorem scalarSiteSchemeKernel_absolute_law {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : 0<β) (h : ℝ) (j : ℕ) (hj : j≤k+1)
    (H : FiniteStateField (Fin 1)) :
    (scalarSiteSchemeKernel s β h j H).map (scalarSiteAbsolute h)=
      mixedSchemeScalarStep (AdmissibleEvenMixture.quadratic (β^2) (sq_pos_of_pos hβ)) s
        (k+1-j) (scalarSiteAbsolute h H) := by
  classical
  let ξ:=AdmissibleEvenMixture.quadratic (β^2) (sq_pos_of_pos hβ)
  let F:=scalarSiteSchemeCascade s β h j
  have hFm : Measurable F := (scalarSiteSchemeCascade_lipschitz s β h j).continuous.measurable
  have hcard (q : Fin 1) : (Finset.univ.filter (fun l : Fin 1=>id l=q)).card=1 := by
    have hq : q=0 := Subsingleton.elim _ _
    rw [hq]
    decide
  have hb (y : FiniteStateField (Fin 1)) (_ : ∀l,y l=y (id (id l))) :
      F y=(∑l : Fin 1,mixedPotential ξ (Paper.parisiSchemeMeasure s) (s.q ((k+1-j)+1),h+y l))+Real.log 2 := by
    dsimp only [F]
    rw [scalarSiteSchemeCascade_eq_potential s β hβ h j (by omega) y]
    simp only [Fin.sum_univ_one,ξ,mixedPotential_quadratic,Real.sqrt_sq_eq_abs,
      abs_of_pos hβ,scalarSiteAbsolute,show k+1-j+1=k+2-j by omega]
    ring
  have he:=mixed_replica_site_baseline_stepLaw ξ s (k+1-j) (by omega)
    (id : Fin 1→Fin 1) id (fun _=>rfl) 1 (by norm_num) hcard h H (fun _=>rfl)
    (Real.log 2) F hFm hb
  have hvar : ξ.first (s.q (k+1-j+1))-ξ.first (s.q (k+1-j))=scalarSchemeVariance s β j := by
    simp only [ξ,AdmissibleEvenMixture.quadratic_first,scalarSchemeVariance,
      show k+1-j+1=k+2-j by omega]
    ring
  rw [hvar] at he
  simp only [Nat.cast_one,div_one] at he
  have hmabs:=measurable_replicaSiteAbsoluteField (d:=1) h
  have hev:=congrArg (fun P : Measure (Fin 1→ℝ)=>P.map (Function.eval (0 : Fin 1))) he
  haveI:=isMarkovKernel_mixedSchemeScalarStep ξ s (p:=k+1-j) (by omega)
  rw [Measure.map_map (measurable_pi_apply _) hmabs,replicaGroupKernel_apply] at hev
  have hcopy : replicaGroupCopy (id : Fin 1→Fin 1)=id := rfl
  rw [hcopy,Measure.map_id,(measurePreserving_eval (μ:=fun q : Fin 1=>
    mixedSchemeScalarStep ξ s (k+1-j) (replicaSiteAbsoluteField h H (id q))) (0 : Fin 1)).map_eq] at hev
  change (finiteStateGaussianStepLaw (scalarSchemeMass s j) (scalarSiteSchemeInput s β j) F H).map
    (scalarSiteAbsolute h)=mixedSchemeScalarStep ξ s (k+1-j) (scalarSiteAbsolute h H) at hev
  change (finiteStateGaussianStepKernel (scalarSchemeMass s j) (scalarSiteSchemeInput s β j) F H).map
    (scalarSiteAbsolute h)=_
  rw [finiteStateGaussianStepKernel_apply _ _ _ hFm]
  exact hev

/-- Every bounded parent-field observable has the literal scalar endpoint
kernel expectation; the test need not be a terminal tanh product. -/
theorem scalarSiteScheme_parent_mean {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : 0<β) (h : ℝ) (p n : ℕ) (hn : p+n≤k+2)
    (f : ℝ→ℝ) (hf : Measurable f) (C : ℝ) (hC : 0≤C) (hb : ∀x,|f x|≤C)
    (H : FiniteStateField (Fin 1)) :
    sourceKernelExpectation (fun i=>scalarSiteSchemeKernel s β h (p+i)) n
      (fun y=>f (scalarSiteAbsolute h y)) H=
      ∫y,f y ∂mixedSchemeEndpointKernel
        (AdmissibleEvenMixture.quadratic (β^2) (sq_pos_of_pos hβ)) s (k+2-(p+n)) n
        (scalarSiteAbsolute h H) := by
  let ξ:=AdmissibleEvenMixture.quadratic (β^2) (sq_pos_of_pos hβ)
  have hmap (i : ℕ) (hi : i<n) (y : FiniteStateField (Fin 1)) :
      (scalarSiteSchemeKernel s β h (p+i) y).map (scalarSiteAbsolute h)=
        mixedSchemeScalarStep ξ s (k+1-p-i) (scalarSiteAbsolute h y) := by
    have he:=scalarSiteSchemeKernel_absolute_law s β hβ h (p+i) (by omega) y
    simpa only [Nat.sub_sub] using he
  rw [sourceKernelExpectation_map_intertwining _ _ _ (measurable_scalarSiteAbsolute h) n hmap f hf H]
  have hr : (fun i=>mixedSchemeScalarStep ξ s (k+1-p-i))=
      fun i=>mixedSchemeScalarStep ξ s ((k+2-(p+n))+n-1-i) := by
    funext i
    congr 1
    omega
  rw [hr]
  exact scalar_reverse_endpoint_mean ξ s (k+2-(p+n)) n (by omega) f hf C hC hb _

end FourPapersCommon
