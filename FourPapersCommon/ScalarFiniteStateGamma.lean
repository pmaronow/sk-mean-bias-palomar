module
public import FourPapersCommon.ScalarFiniteStateCascadeLaw
public import FourPapersCommon.ScalarFiniteStateCovarianceSchedule
public import FourPapersCommon.MixedFiniteDiffusionLaw

@[expose] public section

/-! Genuine Γ moments of parent fields in a scalar Gaussian cascade.
The normalized kernel law is the constructed Brownian diffusion endpoint
law, so the observable is the actual selected magnetization square. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Real
open scoped BigOperators
namespace FourPapersCommon
open OverlapPaper SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 1800000

def scalarSpinAxis : FiniteStateField (Configuration 1) :=
  replicaSingleSiteSpinCLM (EuclideanSpace.single (0 : Fin 1) 1)

theorem fderiv_scalarGaussianTerminalCascade_axis {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : 0<β) (h : ℝ) (j : ℕ) (hj : j≤k+2)
    (H : FiniteStateField (Fin 1)) :
    fderiv ℝ (finiteStateGaussianTerminalCascade (scalarSpinPotential h)
      (scalarSchemeMass s) (scalarSchemeSpinInput s β) j) (replicaSingleSiteSpinCLM H) scalarSpinAxis=
      Paper.parisiGradient β (Paper.parisiSchemeMeasure s) (s.q (k+2-j),scalarSiteAbsolute h H) := by
  let U:=finiteStateGaussianTerminalCascade (scalarSpinPotential h)
    (scalarSchemeMass s) (scalarSchemeSpinInput s β) j
  let e:FiniteStateField (Fin 1):=EuclideanSpace.single 0 1
  have hU:=contDiff_one_finiteStateGaussianTerminalCascade (scalarSpinPotential h)
    (scalarSchemeMass s) (scalarSchemeMass_nonneg s) (scalarSchemeSpinInput s β) j
  have hi:=((hasDerivAt_id (0 : ℝ)).smul_const e).const_add H
  have hiT:=(replicaSingleSiteSpinCLM (d:=1)).hasFDerivAt.comp_hasDerivAt 0 hi
  have hd:=hU.differentiable (by norm_num) _ |>.hasFDerivAt.comp_hasDerivAt 0 hiT
  have hq : s.q (k+2-j)∈Icc (0 : ℝ) 1 :=⟨s.q_nonneg (by omega),s.q_le_one (by omega)⟩
  have hP0 : HasDerivAt (fun y=>Paper.parisiPotential β (Paper.parisiSchemeMeasure s) (s.q (k+2-j),y))
      (Paper.parisiGradient β (Paper.parisiSchemeMeasure s) (s.q (k+2-j),scalarSiteAbsolute h H))
      (scalarSiteAbsolute h H+0) := by
    simpa only [add_zero] using Paper.hasDerivAt_parisiPotential_spatial_all β (Paper.parisiSchemeMeasure s)
      (s.q (k+2-j)) (scalarSiteAbsolute h H) hq
  have hP:=hP0.comp 0 ((hasDerivAt_id (0 : ℝ)).const_add (scalarSiteAbsolute h H))
  have he : (fun x : ℝ=>U (replicaSingleSiteSpinCLM (H+x • e)))=
      fun x=>Real.log 2+Paper.parisiPotential β (Paper.parisiSchemeMeasure s)
        (s.q (k+2-j),scalarSiteAbsolute h H+x) := by
    funext x
    rw [show U (replicaSingleSiteSpinCLM (H+x • e))=
      Real.log 2+Paper.parisiPotential β (Paper.parisiSchemeMeasure s)
        (s.q (k+2-j),h+(H+x • e) 0) from
      scalarGaussianTerminalCascade_scheme s β hβ h j hj (H+x • e)]
    simp only [WithLp.ofLp_add,Pi.add_apply,WithLp.ofLp_smul,Pi.smul_apply,smul_eq_mul,
      e,EuclideanSpace.single_apply,ite_true,mul_one,scalarSiteAbsolute]
    congr 2
    ring
  have hd' : HasDerivAt (fun x : ℝ=>U (replicaSingleSiteSpinCLM (H+x • e)))
      (fderiv ℝ U (replicaSingleSiteSpinCLM H) scalarSpinAxis) 0 := by
    simpa only [U,Function.comp_def,id_eq,one_smul,zero_smul,add_zero,scalarSpinAxis,e] using hd
  rw [he] at hd'
  exact hd'.unique (by simpa only [Function.comp_def,id_eq,zero_add,add_zero,mul_one] using hP.const_add (Real.log 2))

/-- The literal parent Γ, at every cut including the terminal and initial
cuts, under the actual selected Brownian state. -/
theorem scalarSiteScheme_parent_Gamma {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : 0<β) (h : ℝ) (p : ℕ) (hp : p≤k+2) :
    sourceKernelExpectation (fun i=>scalarSiteSchemeKernel s β h (p+i)) (k+2-p)
      (fun y=>Paper.parisiGradient β (Paper.parisiSchemeMeasure s)
        (s.q (k+2-p),scalarSiteAbsolute h y)^2) 0=
      mixedGamma (AdmissibleEvenMixture.quadratic (β^2) (sq_pos_of_pos hβ)) h
        (Paper.parisiSchemeMeasure s) (s.q (k+2-p)) := by
  let ξ:=AdmissibleEvenMixture.quadratic (β^2) (sq_pos_of_pos hβ)
  let f:=fun x=>Paper.parisiGradient β (Paper.parisiSchemeMeasure s) (s.q (k+2-p),x)^2
  have hf : Measurable f := ((Paper.continuous_parisiGradient β (Paper.parisiSchemeMeasure s)).comp
    (continuous_const.prodMk continuous_id)).pow 2 |>.measurable
  have hb (x : ℝ) : |f x|≤1 := by
    have hg:=Paper.norm_parisiGradient_le_one β (Paper.parisiSchemeMeasure s) (s.q (k+2-p),x)
    rw [Real.norm_eq_abs] at hg
    dsimp [f]
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_abs (Paper.parisiGradient β (Paper.parisiSchemeMeasure s) (s.q (k+2-p),x)),
      abs_nonneg (Paper.parisiGradient β (Paper.parisiSchemeMeasure s) (s.q (k+2-p),x))]
  have he:=scalarSiteScheme_parent_mean s β hβ h p (k+2-p) (by omega) f hf 1 zero_le_one hb 0
  simp only [Nat.add_sub_of_le hp,Nat.sub_self,scalarSiteAbsolute,WithLp.ofLp_zero,Pi.zero_apply,add_zero] at he
  change sourceKernelExpectation (fun i=>scalarSiteSchemeKernel s β h (p+i)) (k+2-p)
    (fun y=>f (h+y 0)) 0=_
  rw [he]
  rw [←mixedState_schemeEndpoint_law ξ h s (p:=k+2-p) (by omega)]
  rw [integral_map (measurable_mixedState ξ h _ ⟨s.q_nonneg (by omega),s.q_le_one (by omega)⟩).aemeasurable hf.aestronglyMeasurable]
  unfold mixedGamma
  congr 1
  funext sample
  dsimp only [f,ξ]
  simp only [mixedGradient_quadratic,Real.sqrt_sq_eq_abs,abs_of_pos hβ]

end FourPapersCommon
