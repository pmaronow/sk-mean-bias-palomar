module
public import QuantitativePaper.VectorFiniteHessianResponse
public import QuantitativePaper.VectorLinearGeneratorCalculus

@[expose] public section

/-! Actual finite-cell Hessian reaction PDE. It is obtained from the
genuine Gaussian response and its square, not an assumed mixed derivative. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

def vectorFiniteCellHessianDiagonal (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (i : ℕ) (q : ℝ) (x : Field n) (l : Fin n) : ℝ :=
  (hessianOperator (vectorFiniteCellPotential s β t p i q) x (EuclideanSpace.single l 1)) l

theorem contDiff_vectorFiniteCellGradient_component (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (i : ℕ) (q : ℝ) (l : Fin n) :
    ContDiff ℝ ∞ (fun y=>gradient (vectorFiniteCellPotential s β t p i q) y l) := by
  have hf:=contDiff_vectorColeHopfStep_recursion_field s β t
    (((1-t)*β^2)*(s.q (i+1)-q)) (s.m i) p (k+1-i)
  have hg : ContDiff ℝ ∞ (gradient (vectorFiniteCellPotential s β t p i q)):=
    (InnerProductSpace.toDual ℝ (Field n)).symm.contDiff.comp (hf.fderiv_right (m:=∞) (by simp))
  exact (EuclideanSpace.proj l).contDiff.comp hg

theorem hasDerivAt_vectorFiniteCellHessian_time (s : RSBScheme k) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (p : Couplings n×ℝ) (i : ℕ)
    (q : ℝ) (hq : q<s.q (i+1)) (x : Field n) (l : Fin n) :
    HasDerivAt (fun r=>vectorFiniteCellHessianDiagonal s β t p i r x l)
      (-((1-t)*β^2)*vectorLinearBackwardGenerator
        (fun y=>vectorFiniteCellHessianDiagonal s β t p i q y l)
        (vectorFiniteCellPotential s β t p i q) (s.m i) x-
      ((1-t)*β^2)*(s.m i)*∑j : Fin n,
        (fderiv ℝ (fun y=>gradient (vectorFiniteCellPotential s β t p i q) y l) x
          (EuclideanSpace.single j 1))^2) q := by
  let c:=(1-t)*β^2
  let m:=s.m i
  let f:=vectorRecursion s β t p (k+1-i)
  let A:=fun y=>vectorFiniteHessianResponseObservable s β t i l (p,y)
  let U:=vectorFiniteCellPotential s β t p i q
  let R:=vectorStepResponse (c*(s.q (i+1)-q)) m f A
  let g:=fun y=>gradient U y l
  let data:=(vectorFiniteHessianResponseData s β t i l).fieldData p
  have hv:0<c*(s.q (i+1)-q):=
    mul_pos (mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hβ)) (sub_pos.mpr hq)
  have hRraw:=(hasDerivAt_vectorStepResponse_variance f A m
    (data.weightedDatum m) (data.expDatum m) hv x).comp q
      (((hasDerivAt_id q).const_sub (s.q (i+1))).const_mul c)
  have hR : HasDerivAt (fun r=>vectorStepResponse (c*(s.q (i+1)-r)) m f A x)
      (-c*vectorLinearBackwardGenerator R U m x) q:=by
    convert hRraw using 1
    · rfl
    · dsimp only [vectorLinearBackwardGenerator]
      rw [show U=vectorColeHopfStep (c*(s.q (i+1)-q)) m f from rfl]
      change -c*(vectorBilinearTrace (vectorHessian R x)/2+
        fderiv ℝ R x (m • gradient (vectorColeHopfStep (c*(s.q (i+1)-q)) m f) x))=
        (vectorBilinearTrace (vectorHessian R x)/2+
        fderiv ℝ R x (m • gradient (vectorColeHopfStep (c*(s.q (i+1)-q)) m f) x))*(c*(-1))
      ring
  have hg:=hasDerivAt_vectorFiniteCellGradient_time s β t hβ ht p i q hq x l
  have hcomb:=hR.sub ((hg.pow 2).const_mul m)
  have hfun : (fun r=>vectorStepResponse (c*(s.q (i+1)-r)) m f A x-
      m*(gradient (vectorFiniteCellPotential s β t p i r) x l)^2)=
      (fun r=>vectorFiniteCellHessianDiagonal s β t p i r x l):=by
    funext r
    exact (vectorFiniteCellHessian_diagonal_eq_response s β t p i r x l).symm
  change HasDerivAt (fun r=>vectorStepResponse (c*(s.q (i+1)-r)) m f A x-
      m*(gradient (vectorFiniteCellPotential s β t p i r) x l)^2) _ q at hcomb
  rw [hfun] at hcomb
  have hR2 : ContDiff ℝ 2 R:=((data.bounds m).responseRegularity _).of_le (by norm_num)
  have hg2 : ContDiff ℝ 2 g:=
    (contDiff_vectorFiniteCellGradient_component s β t p i q l).of_le (by simp)
  have hH : (fun y=>vectorFiniteCellHessianDiagonal s β t p i q y l)=
      (fun y=>R y-m*g y^2):=by
    funext y
    exact vectorFiniteCellHessian_diagonal_eq_response s β t p i q y l
  have hgen : vectorLinearBackwardGenerator (fun y=>vectorFiniteCellHessianDiagonal s β t p i q y l) U m x=
      vectorLinearBackwardGenerator R U m x-
        m*(2*g x*vectorLinearBackwardGenerator g U m x+
          ∑j : Fin n,(fderiv ℝ g x (EuclideanSpace.single j 1))^2):=by
    rw [hH,vectorLinearBackwardGenerator_sub R (fun y=>m*g y^2) U hR2
      (contDiff_const.mul (hg2.pow 2)),
      vectorLinearBackwardGenerator_const_mul (fun y=>g y^2) U (hg2.pow 2),
      vectorLinearBackwardGenerator_square g U hg2]
  apply hcomb.congr_deriv
  norm_num only [Nat.cast_ofNat,pow_one,show 2-1=1 by omega]
  change -c*vectorLinearBackwardGenerator R U m x-
    m*(2*g x*(-c*vectorLinearBackwardGenerator g U m x))=
      -c*vectorLinearBackwardGenerator (fun y=>vectorFiniteCellHessianDiagonal s β t p i q y l) U m x-
        c*m*∑j : Fin n,(fderiv ℝ g x (EuclideanSpace.single j 1))^2
  rw [hgen]
  ring

end QuantitativePaper
