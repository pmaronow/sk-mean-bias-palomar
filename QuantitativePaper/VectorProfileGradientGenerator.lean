module
public import QuantitativePaper.VectorProfileCellLegendreCoordinates
public import QuantitativePaper.VectorFiniteGradientResponse
public import FourPapersCommon.GeneratorPullback
public import FourPapersCommon.LinearDerivativeComposition
public import FourPapersCommon.HessianPushforwardTrace

@[expose] public section

/-! The actual finite-profile gradient has zero diffusion generator on
every strict cell. Its time equation comes from genuine Gaussian heat
differentiation, and all coordinate derivatives are literal Fréchet jets. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem hasDerivAt_vectorProfileCellGradient_component_time
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (a : VectorProfileCellParameter n) (hq : a.1<s₀.q (i+1))
    (hθ : a.2.1∈Icc (0 : ℝ) 1) (x : Field n) (l : Fin n) :
    HasDerivAt (fun r=>vectorProfileCellJointGradient s₀ s₁ β t i ((r,a.2),x) l)
      (-((1-t)*β^2)*vectorLinearBackwardGenerator
        (fun y=>vectorProfileCellJointGradient s₀ s₁ β t i (a,y) l)
        (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (a,y))
        (vectorProfileMass s₀ s₁ a.2.1 i) x) a.1 := by
  let S:=vectorProfileScheme s₀ s₁ a.2.1 hθ
  have he (r : ℝ) : (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i ((r,a.2),y))=
      vectorFiniteCellPotential S β t a.2.2 i r:=by
    funext y
    exact vectorProfilePhysicalCell_eq_finiteCell s₀ s₁ β t i r a.2.1 hθ a.2.2 y
  have hg (r : ℝ) (y : Field n) :
      vectorProfileCellJointGradient s₀ s₁ β t i ((r,a.2),y)=
        gradient (vectorFiniteCellPotential S β t a.2.2 i r) y:=by
    unfold vectorProfileCellJointGradient
    rw [he]
  simp_rw [hg,he]
  exact hasDerivAt_vectorFiniteCellGradient_time S β t hβ ht a.2.2 i a.1 hq x l

theorem vectorProfileCellGradient_generator_zero
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (a : VectorProfileCellParameter n)
    (hq : a.1<s₀.q (i+1)) (hθ : a.2.1∈Ioo (0 : ℝ) 1) (x : Field n) :
    deriv (fun r=>vectorProfileCellJointGradient s₀ s₁ β t i ((r,a.2),x)) a.1+
      fderiv ℝ (fun y=>vectorProfileCellJointGradient s₀ s₁ β t i (a,y)) x
        (((1-t)*β^2*vectorProfileMass s₀ s₁ a.2.1 i) •
          vectorProfileCellJointGradient s₀ s₁ β t i (a,x))+
      (((1-t)*β^2)/2) • (∑j : Fin n,
        fderiv ℝ (fderiv ℝ (fun y=>vectorProfileCellJointGradient s₀ s₁ β t i (a,y))) x
          (EuclideanSpace.single j 1) (EuclideanSpace.single j 1))=0 := by
  let G : ℝ×Field n→Field n:=fun z=>vectorProfileCellJointGradient s₀ s₁ β t i ((z.1,a.2),z.2)
  let U : Field n→ℝ:=fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (a,y)
  let c:=(1-t)*β^2
  let m:=vectorProfileMass s₀ s₁ a.2.1 i
  have hG : ContDiffAt ℝ ∞ G (a.1,x):=ContDiffAt.comp
    (f := fun z : ℝ×Field n=>((z.1,a.2),z.2))
    (g := vectorProfileCellJointGradient s₀ s₁ β t i) (a.1,x)
    (contDiffAt_vectorProfileCellJointGradient s₀ s₁ β t hβ ht i hi (a,x) hq hθ)
    (by fun_prop)
  have hg : ContDiffAt ℝ 2 (fun y=>G (a.1,y)) x:=
    (hG.comp x (contDiffAt_const.prodMk contDiffAt_id)).of_le (by norm_num)
  have hgt:=(hG.comp a.1 (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  apply PiLp.ext
  intro l
  have hdproj:=(EuclideanSpace.proj l).hasFDerivAt.comp_hasDerivAt a.1 hgt.hasDerivAt
  have hdcomp:=hasDerivAt_vectorProfileCellGradient_component_time s₀ s₁ β t hβ ht i a hq
    ⟨hθ.1.le,hθ.2.le⟩ x l
  have htime : (deriv (fun r=>G (r,x)) a.1) l=
      -c*vectorLinearBackwardGenerator (fun y=>G (a.1,y) l) U m x:=
    hdproj.unique hdcomp
  have hfirst (w : Field n):=fderiv_linear_postcomp (EuclideanSpace.proj l)
    (fun y=>G (a.1,y)) x w (hg.differentiableAt (by norm_num))
  have hsecond (j : Fin n):=second_fderiv_linear_postcomp (EuclideanSpace.proj l)
    (fun y=>G (a.1,y)) x (EuclideanSpace.single j 1) hg
  change ∀w,fderiv ℝ (fun y=>G (a.1,y) l) x w=(fderiv ℝ (fun y=>G (a.1,y)) x w) l at hfirst
  change ∀j,fderiv ℝ (fderiv ℝ (fun y=>G (a.1,y) l)) x
    (EuclideanSpace.single j 1) (EuclideanSpace.single j 1)=
      (fderiv ℝ (fderiv ℝ (fun y=>G (a.1,y))) x
        (EuclideanSpace.single j 1) (EuclideanSpace.single j 1)) l at hsecond
  change ((deriv (fun r=>G (r,x)) a.1)+fderiv ℝ (fun y=>G (a.1,y)) x ((c*m) • G (a.1,x))+
    (c/2) • (∑j : Fin n,fderiv ℝ (fderiv ℝ (fun y=>G (a.1,y))) x
      (EuclideanSpace.single j 1) (EuclideanSpace.single j 1))) l=0
  simp only [PiLp.add_apply,PiLp.smul_apply,WithLp.ofLp_sum,Finset.sum_apply,smul_eq_mul]
  rw [htime,←hfirst]
  simp_rw [←hsecond]
  unfold vectorLinearBackwardGenerator vectorBilinearTrace vectorHessian
  have hgrad : gradient U x=G (a.1,x):=rfl
  rw [hgrad]
  simp only [map_smul,smul_eq_mul]
  ring

end QuantitativePaper
