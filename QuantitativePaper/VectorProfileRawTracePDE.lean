module
public import QuantitativePaper.VectorProfileRawTraceCalculus
public import QuantitativePaper.VectorProfileTimePullbacks

@[expose] public section

/-! The literal trace reaction equation of the genuine finite profile. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem hasDerivAt_vectorFiniteCellHessianTrace_time
    (s : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (p : Couplings n×ℝ) (i : ℕ) (q : ℝ) (hq : q<s.q (i+1)) (x : Field n) :
    HasDerivAt (fun r=>euclideanOperatorTrace
      (hessianOperator (vectorFiniteCellPotential s β t p i r) x))
      (-((1-t)*β^2)*vectorLinearBackwardGenerator
        (fun y=>euclideanOperatorTrace
          (hessianOperator (vectorFiniteCellPotential s β t p i q) y))
        (vectorFiniteCellPotential s β t p i q) (s.m i) x-
        ((1-t)*β^2)*(s.m i)*euclideanOperatorTrace
          (hessianOperator (vectorFiniteCellPotential s β t p i q) x*
            hessianOperator (vectorFiniteCellPotential s β t p i q) x)) q := by
  let U:=vectorFiniteCellPotential s β t p i q
  have hU : ContDiff ℝ 4 U:=
    (contDiff_vectorColeHopfStep_recursion_field s β t _ _ p (k+1-i)).of_le (by simp)
  have hA (l : Fin n) : ContDiff ℝ 2 (fun y=>vectorFiniteCellHessianDiagonal s β t p i q y l):=by
    exact (EuclideanSpace.proj l).contDiff.comp
      ((contDiff_hessianOperator U hU).clm_apply contDiff_const)
  have hd:=HasDerivAt.fun_sum (u:=Finset.univ) (fun l _=>
    hasDerivAt_vectorFiniteCellHessian_time s β t hβ ht p i q hq x l)
  have he (r : ℝ) : euclideanOperatorTrace
      (hessianOperator (vectorFiniteCellPotential s β t p i r) x)=
        ∑l : Fin n,vectorFiniteCellHessianDiagonal s β t p i r x l:=rfl
  have hef : (fun y=>euclideanOperatorTrace (hessianOperator U y))=
      (fun y=>∑l : Fin n,vectorFiniteCellHessianDiagonal s β t p i q y l):=rfl
  simp_rw [←he] at hd
  apply hd.congr_deriv
  rw [hef,vectorLinearBackwardGenerator_fin_sum Finset.univ _ U (fun l _=>hA l),
    euclideanOperatorTrace_hessian_square_eq U x (hU.contDiffAt.of_le (by norm_num))]
  simp only [Finset.sum_sub_distrib,←Finset.mul_sum]
  rfl

theorem vectorProfileCellRawTrace_time_PDE
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (a : VectorProfileCellParameter n) (hq : a.1<s₀.q (i+1))
    (hθ : a.2.1∈Icc (0 : ℝ) 1) (x : Field n) :
    deriv (fun q=>vectorProfileCellRawTrace s₀ s₁ β t i (q,a.2) x) a.1=
      -((1-t)*β^2)/2*(vectorLaplacian
        (vectorProfileCellRawTrace s₀ s₁ β t i a) x+
        2*vectorProfileMass s₀ s₁ a.2.1 i*
          (euclideanOperatorTrace
            (hessianOperator (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (a,y)) x*
              hessianOperator (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (a,y)) x)+
            inner ℝ (vectorProfileCellJointGradient s₀ s₁ β t i (a,x))
              (gradient (vectorProfileCellRawTrace s₀ s₁ β t i a) x))) := by
  let S:=vectorProfileScheme s₀ s₁ a.2.1 hθ
  have he (r : ℝ) : (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i ((r,a.2),y))=
      vectorFiniteCellPotential S β t a.2.2 i r:=by
    funext y
    exact vectorProfilePhysicalCell_eq_finiteCell s₀ s₁ β t i r a.2.1 hθ a.2.2 y
  have htrace (r : ℝ) (y : Field n) : vectorProfileCellRawTrace s₀ s₁ β t i (r,a.2) y=
      euclideanOperatorTrace (hessianOperator (vectorFiniteCellPotential S β t a.2.2 i r) y):=by
    unfold vectorProfileCellRawTrace
    rw [he]
  have htfun : (fun q=>vectorProfileCellRawTrace s₀ s₁ β t i (q,a.2) x)=
      (fun q=>euclideanOperatorTrace (hessianOperator (vectorFiniteCellPotential S β t a.2.2 i q) x)):=
    funext (fun q=>htrace q x)
  have htf (r : ℝ) : vectorProfileCellRawTrace s₀ s₁ β t i (r,a.2)=
      (fun y=>euclideanOperatorTrace (hessianOperator (vectorFiniteCellPotential S β t a.2.2 i r) y)):=
    funext (fun y=>htrace r y)
  rw [htfun,(hasDerivAt_vectorFiniteCellHessianTrace_time S β t hβ ht a.2.2 i a.1 hq x).deriv]
  have ha : (a.1,a.2)=a:=Prod.eta a
  rw [←ha]
  simp only [vectorProfileCellJointGradient,he,htf]
  unfold vectorLinearBackwardGenerator
  have hLap (f : Field n→ℝ) (y : Field n) :
      vectorBilinearTrace (vectorHessian f y)=vectorLaplacian f y:=rfl
  rw [hLap]
  simp only [map_smul,smul_eq_mul,←inner_gradient_left,real_inner_comm]
  change _=-((1-t)*β^2)/2*(_+2*S.m i*(_+_))
  ring

end QuantitativePaper
