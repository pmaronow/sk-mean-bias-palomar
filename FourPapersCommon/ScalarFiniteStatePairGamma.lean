module
public import FourPapersCommon.ScalarFiniteStateGamma
public import FourPapersCommon.FiniteStateCascadeGibbsTransport
public import FourPapersCommon.FiniteStateCascadeRecurrence

@[expose] public section

/-! The actual one-spin split-replica covariance is the actual diffusion Γ.
The Gaussian cascade kernels are transported through their genuine linear
spin embedding, rather than identified by a supplied representation premise. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Real
open scoped BigOperators
namespace FourPapersCommon
open OverlapPaper SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 1800000

def scalarSpinSchemeKernel {k : ℕ} (s : RSBScheme k) (β h : ℝ) (j : ℕ) :=
  finiteStateGaussianCascadeKernel (scalarSchemeMass s) (scalarSchemeSpinInput s β)
    (gtStateLogPartition (scalarSpinPotential h)) j

theorem scalarSpinSchemeKernel_linear_law {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (j : ℕ) (H : FiniteStateField (Fin 1)) :
    (scalarSiteSchemeKernel s β h j H).map (replicaSingleSiteSpinCLM (d:=1))=
      scalarSpinSchemeKernel s β h j (replicaSingleSiteSpinCLM H) := by
  let T:=replicaSingleSiteSpinCLM (d:=1)
  let U:=finiteStateGaussianTerminalCascade (scalarSpinPotential h) (scalarSchemeMass s)
    (scalarSchemeSpinInput s β) j
  have hUc : Measurable U := (contDiff_one_finiteStateGaussianTerminalCascade (scalarSpinPotential h)
    (scalarSchemeMass s) (scalarSchemeMass_nonneg s) (scalarSchemeSpinInput s β) j).continuous.measurable
  have hFc:= (scalarSiteSchemeCascade_lipschitz s β h j).continuous.measurable
  have hF : (fun y=>gtStateLogPartition (scalarSpinPotential h) (T y))=
      replicaSourceSingleSite h 0 (∅ : Finset (Fin 1)) := by
    funext y
    rw [replicaSourceSingleSite_eq_terminal]
    simp only [zero_mul,add_zero]
    rfl
  have he : (fun y=>U (T y))=scalarSiteSchemeCascade s β h j := by
    funext y
    have hh:=finiteStateGaussianCascade_comp_linear T (scalarSiteSchemeInput s β)
      (scalarSchemeMass s) (gtStateLogPartition (scalarSpinPotential h)) j y
    rw [hF] at hh
    exact hh
  change (finiteStateGaussianStepKernel (scalarSchemeMass s j) (scalarSiteSchemeInput s β j)
    (scalarSiteSchemeCascade s β h j) H).map T=
      finiteStateGaussianStepKernel (scalarSchemeMass s j) (scalarSchemeSpinInput s β j) U (T H)
  rw [finiteStateGaussianStepKernel_apply _ _ _ hFc,finiteStateGaussianStepKernel_apply _ _ _ hUc,
    ←he]
  exact finiteStateGaussianStepLaw_comp_linear T (scalarSiteSchemeInput s β j) (scalarSchemeMass s j) U hUc H

theorem scalarSpinScheme_parent_mean {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (p n : ℕ) (f : FiniteStateField (Configuration 1)→ℝ) (hf : Measurable f)
    (H : FiniteStateField (Fin 1)) :
    sourceKernelExpectation (fun i=>scalarSpinSchemeKernel s β h (p+i)) n f (replicaSingleSiteSpinCLM H)=
      sourceKernelExpectation (fun i=>scalarSiteSchemeKernel s β h (p+i)) n
        (fun y=>f (replicaSingleSiteSpinCLM y)) H :=
  (sourceKernelExpectation_map_intertwining _ _ _
    (replicaSingleSiteSpinCLM (d:=1)).continuous.measurable n
    (fun i _ y=>scalarSpinSchemeKernel_linear_law s β h (p+i) y) f hf H).symm

/-- Two independent terminal replicas, conditioned on the common cascade
field, have the exact actual squared selected magnetization moment. -/
theorem scalarGaussianCascade_pairMoment_Gamma {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : 0<β) (h : ℝ) (p : ℕ) (hp : p≤k+2) :
    finiteStateCascadePairMoment (scalarSpinPotential h) (scalarSchemeMass s)
      (scalarSchemeSpinInput s β) p (k+2-p) 0 scalarSpinAxis scalarSpinAxis=
      mixedGamma (AdmissibleEvenMixture.quadratic (β^2) (sq_pos_of_pos hβ)) h
        (Paper.parisiSchemeMeasure s) (s.q (k+2-p)) := by
  let U:=finiteStateGaussianTerminalCascade (scalarSpinPotential h) (scalarSchemeMass s)
    (scalarSchemeSpinInput s β) p
  let f:=fun y=>fderiv ℝ U y scalarSpinAxis*fderiv ℝ U y scalarSpinAxis
  have hU:=contDiff_one_finiteStateGaussianTerminalCascade (scalarSpinPotential h)
    (scalarSchemeMass s) (scalarSchemeMass_nonneg s) (scalarSchemeSpinInput s β) p
  have hf : Measurable f := ((hU.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul
    ((hU.continuous_fderiv (by norm_num)).clm_apply continuous_const) |>.measurable
  change sourceKernelExpectation (fun i=>scalarSpinSchemeKernel s β h (p+i)) (k+2-p) f 0=_
  have he:=scalarSpinScheme_parent_mean s β h p (k+2-p) f hf 0
  rw [map_zero] at he
  rw [he]
  have heF : (fun y=>f (replicaSingleSiteSpinCLM y))=
      fun y=>Paper.parisiGradient β (Paper.parisiSchemeMeasure s)
        (s.q (k+2-p),scalarSiteAbsolute h y)^2 := by
    funext y
    dsimp only [f,U]
    rw [fderiv_scalarGaussianTerminalCascade_axis s β hβ h p hp y]
    ring
  rw [heF]
  exact scalarSiteScheme_parent_Gamma s β hβ h p hp

end FourPapersCommon
