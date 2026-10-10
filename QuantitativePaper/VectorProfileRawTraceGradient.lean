module
public import QuantitativePaper.VectorProfileRawTracePDE

@[expose] public section

/-! A retained-field formula for the actual time derivative of the profile
potential. No time jet is needed to bound its gradient at a cell endpoint. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

theorem gradient_gradient_norm_sq (U : Field n → ℝ) (x : Field n)
    (hU : ContDiffAt ℝ 2 U x) :
    gradient (fun y=>‖gradient U y‖^2) x=(2 : ℝ) • hessianOperator U x (gradient U x) := by
  apply ext_inner_right ℝ
  intro w
  rw [real_inner_smul_left,inner_gradient_left,
    (hasFDerivAt_gradient_of_contDiffAt U x hU).norm_sq.fderiv]
  simp only [two_smul]
  change inner ℝ (gradient U x) (hessianOperator U x w)+
    inner ℝ (gradient U x) (hessianOperator U x w)=
      2*inner ℝ (hessianOperator U x (gradient U x)) w
  have hs : inner ℝ (gradient U x) (hessianOperator U x w)=
      inner ℝ (hessianOperator U x (gradient U x)) w:=by
    rw [←real_inner_comm (gradient U x) (hessianOperator U x w),inner_hessianOperator,
      inner_hessianOperator,(hU.isSymmSndFDerivAt (by norm_num)).eq w (gradient U x)]
  rw [hs]
  ring

theorem gradient_affine_sum_at (f g : Field n → ℝ) (x : Field n) (c d : ℝ)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    gradient (fun y=>c*(f y+d*g y)) x=c • (gradient f x+d • gradient g x) := by
  apply ext_inner_right ℝ
  intro w
  rw [real_inner_smul_left,inner_add_left,real_inner_smul_left,inner_gradient_left,
    inner_gradient_left,inner_gradient_left]
  have hD:=((hf.hasFDerivAt.add (hg.hasFDerivAt.const_smul d)).const_smul c)
  have he : (fun y=>c*(f y+d*g y))=c • (f+d • g):=funext fun y=>rfl
  rw [he,hD.fderiv]
  rfl

theorem vectorProfileCellPotentialTime_gradient_formula
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (a : VectorProfileCellParameter n) (hq : a.1<s₀.q (i+1))
    (hθ : a.2.1∈Icc (0 : ℝ) 1) (x : Field n) :
    gradient (vectorProfileCellPotentialTime s₀ s₁ β t i a) x=
      (-((1-t)*β^2)/2) • (gradient (vectorProfileCellRawTrace s₀ s₁ β t i a) x+
        (2*vectorProfileMass s₀ s₁ a.2.1 i) •
          hessianOperator (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (a,y)) x
            (vectorProfileCellJointGradient s₀ s₁ β t i (a,x))) := by
  let U : Field n→ℝ:=fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (a,y)
  let T : Field n→ℝ:=vectorProfileCellRawTrace s₀ s₁ β t i a
  let G : Field n→Field n:=gradient U
  have he : U=vectorFiniteCellPotential (vectorProfileScheme s₀ s₁ a.2.1 hθ)
      β t a.2.2 i a.1:=by
    funext y
    exact vectorProfilePhysicalCell_eq_finiteCell s₀ s₁ β t i a.1 a.2.1 hθ a.2.2 y
  have hU : ContDiff ℝ 4 U:=by
    rw [he]
    exact (contDiff_vectorColeHopfStep_recursion_field _ β t _ _ a.2.2 (k+1-i)).of_le (by simp)
  have hT : ContDiff ℝ 2 T:=euclideanOperatorTraceCLM.contDiff.comp
    (contDiff_hessianOperator U hU)
  have hG : ContDiff ℝ 2 G:=contDiff_gradient_two U (hU.of_le (by norm_num))
  have hf : vectorProfileCellPotentialTime s₀ s₁ β t i a=
      (fun y=>-((1-t)*β^2)/2*(T y+vectorProfileMass s₀ s₁ a.2.1 i*‖G y‖^2)):=by
    funext y
    have hd:=(hasDerivAt_vectorProfilePhysicalCell_PDE s₀ s₁ β t hβ ht i
      a.1 a.2.1 hθ hq a.2.2 y).deriv
    change _=-((1-t)*β^2)/2*(vectorLaplacian U y+
      vectorProfileMass s₀ s₁ a.2.1 i*‖G y‖^2) at hd
    rw [←euclideanOperatorTrace_hessian_eq_laplacian] at hd
    exact hd
  rw [hf,gradient_affine_sum_at T (fun y=>‖G y‖^2) x _ _
    (hT.differentiable (by norm_num) x) (hG.differentiable (by norm_num) x |>.norm_sq ℝ)]
  rw [gradient_gradient_norm_sq U x (hU.contDiffAt.of_le (by norm_num)),smul_smul]
  simp only [mul_comm,vectorProfileCellJointGradient,U,T]

end QuantitativePaper
