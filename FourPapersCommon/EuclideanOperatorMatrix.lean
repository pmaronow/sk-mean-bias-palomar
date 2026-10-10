module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import QuantitativeFollowup.CanonicalPosteriorBL
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

/-! Exact coordinate matrices of genuine Euclidean continuous linear maps. -/
noncomputable section
open scoped BigOperators ContDiff Matrix.Norms.Elementwise
namespace FourPapersCommon
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}
local notation "Vec" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

local instance operatorNormedGroup : NormedAddCommGroup (Vec→L[ℝ]Vec):=
  ContinuousLinearMap.toNormedAddCommGroup
local instance operatorNormedSpace : NormedSpace ℝ (Vec→L[ℝ]Vec):=
  ContinuousLinearMap.toNormedSpace

private theorem hasDerivAt_comp_boundedLinear {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : X→L[ℝ]Y) {f : ℝ→X} {v : X} {a : ℝ} (hf : HasDerivAt f v a) :
    HasDerivAt (fun t=>L (f t)) (L v) a := by
  exact L.hasFDerivAt.comp_hasDerivAt a hf

def euclideanOperatorMatrix (L : Vec→L[ℝ]Vec) : Mat:=fun i j=>(L (EuclideanSpace.single j 1)) i

def euclideanOperatorMatrixCLM : (Vec→L[ℝ]Vec)→L[ℝ]Mat:=
  ({toFun:=euclideanOperatorMatrix
    map_add':=by intro L M; ext i j; simp [euclideanOperatorMatrix]
    map_smul':=by intro c L; ext i j; simp [euclideanOperatorMatrix]} :
      (Vec→L[ℝ]Vec)→ₗ[ℝ]Mat).toContinuousLinearMap

theorem euclideanOperatorMatrix_mul (L M : Vec→L[ℝ]Vec) :
    euclideanOperatorMatrix (L*M)=euclideanOperatorMatrix L*euclideanOperatorMatrix M := by
  ext i j
  change (L (M (EuclideanSpace.single j 1))) i=
    ∑ a : Fin n,(L (EuclideanSpace.single a 1)) i*(M (EuclideanSpace.single j 1)) a
  have hw : M (EuclideanSpace.single j 1)=
      ∑ a : Fin n,(M (EuclideanSpace.single j 1)) a • EuclideanSpace.single a 1:=by
    ext b
    simp [Pi.single_apply]
  conv_lhs => rw [hw]
  rw [map_sum]
  simp only [WithLp.ofLp_sum,Finset.sum_apply,map_smul,PiLp.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem euclideanOperatorMatrix_one : euclideanOperatorMatrix (1 : Vec→L[ℝ]Vec)=(1 : Mat):=by
  ext i j
  simp [euclideanOperatorMatrix,Matrix.one_apply,EuclideanSpace.single_apply,eq_comm]

theorem euclideanOperatorMatrix_add (L M : Vec→L[ℝ]Vec) :
    euclideanOperatorMatrix (L+M)=euclideanOperatorMatrix L+euclideanOperatorMatrix M:=by
  ext i j
  simp [euclideanOperatorMatrix]

theorem euclideanOperatorMatrix_smul (c : ℝ) (L : Vec→L[ℝ]Vec) :
    euclideanOperatorMatrix (c • L)=c • euclideanOperatorMatrix L:=by
  ext i j
  simp [euclideanOperatorMatrix]

theorem euclideanOperatorMatrix_sub (L M : Vec→L[ℝ]Vec) :
    euclideanOperatorMatrix (L-M)=euclideanOperatorMatrix L-euclideanOperatorMatrix M:=by
  ext i j
  simp [euclideanOperatorMatrix]

theorem euclideanOperatorMatrix_neg (L : Vec→L[ℝ]Vec) :
    euclideanOperatorMatrix (-L)=-euclideanOperatorMatrix L:=by
  ext i j
  simp [euclideanOperatorMatrix]

theorem hasDerivAt_euclideanOperatorMatrix {f : ℝ→Vec→L[ℝ]Vec} {L : Vec→L[ℝ]Vec} {a : ℝ}
    (hf : HasDerivAt f L a) :
    HasDerivAt (fun t=>euclideanOperatorMatrix (f t)) (euclideanOperatorMatrix L) a:=by
  exact hasDerivAt_comp_boundedLinear (X := Vec→L[ℝ]Vec) (Y := Mat)
    (euclideanOperatorMatrixCLM (n:=n)) hf

theorem euclideanOperatorMatrix_hessian_symmetric (f : Vec→ℝ) (x : Vec)
    (hf : ContDiffAt ℝ 2 f x) :
    (euclideanOperatorMatrix (QuantitativeFollowup.hessianOperator f x)).IsSymm := by
  ext i j
  change (QuantitativeFollowup.hessianOperator f x (EuclideanSpace.single i 1)) j=
    (QuantitativeFollowup.hessianOperator f x (EuclideanSpace.single j 1)) i
  have hi:=QuantitativeFollowup.inner_hessianOperator f x (EuclideanSpace.single i 1)
    (EuclideanSpace.single j 1)
  have hj:=QuantitativeFollowup.inner_hessianOperator f x (EuclideanSpace.single j 1)
    (EuclideanSpace.single i 1)
  simp only [EuclideanSpace.inner_single_right,starRingEnd_apply,star_trivial,one_mul] at hi hj
  rw [hi,hj]
  exact (hf.isSymmSndFDerivAt (by norm_num)).eq _ _

end FourPapersCommon
