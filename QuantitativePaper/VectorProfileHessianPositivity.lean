module
public import QuantitativePaper.VectorProfileCurvaturePairingPDE
public import QuantitativePaper.VectorCovarianceTrace
public import QuantitativePaper.VectorTraceOrder

@[expose] public section

/-! Strict positivity of the literal physical response Hessian and the
canonical Frobenius form of the actual second-variation source. -/
noncomputable section
open Set Filter Matrix
open scoped Topology ContDiff BigOperators MatrixOrder Matrix.Norms.Elementwise
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorProfileCellHessianMatrix_posDef (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (hβ : 0<β) (i : ℕ) (a : VectorProfileCellParameter n)
    (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    (vectorProfileCellHessianMatrix s₀ s₁ β t i a m).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  constructor
  · have hs:=vectorProfileCellHessianMatrix_symmetric s₀ s₁ β t hβ.ne' i a m hm
    change (vectorProfileCellHessianMatrix s₀ s₁ β t i a m).conjTranspose=
      vectorProfileCellHessianMatrix s₀ s₁ β t i a m
    ext l j
    change (vectorProfileCellHessianMatrix s₀ s₁ β t i a m) j l=
      (vectorProfileCellHessianMatrix s₀ s₁ β t i a m) l j
    simpa only [Matrix.transpose_apply] using congrFun (congrFun hs.eq l) j
  · intro v hv
    let w : Field n:=WithLp.toLp 2 v
    have hw : w≠0:=by
      intro he
      apply hv
      ext l
      exact congrArg (fun x : Field n=>x l) he
    rw [real_matrix_quadratic_eq_sum]
    change 0<∑l : Fin n,∑j : Fin n,
      (vectorProfileCellPhysicalHessian s₀ s₁ β t i a m (EuclideanSpace.single j 1)) l*w l*w j
    rw [←euclidean_clm_quadratic_eq_sum,
      vectorProfileCellPhysicalHessian_eq s₀ s₁ β t hβ.ne' i a m hm]
    simp only [ContinuousLinearMap.smul_apply,real_inner_smul_right]
    exact mul_pos hβ (vectorFieldHessian_quadratic_pos _ β t a.2.2 _ _ w hw)

theorem vectorProfileCellBMatrix_symmetric (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (i : ℕ) (hi : i≤k+1)
    (a : VectorProfileCellParameter n) (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1)))
    (hθ : a.2.1∈Ioo (0 : ℝ) 1) (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    (vectorProfileCellBMatrix s₀ s₁ β t i a m).IsSymm :=
  euclideanOperatorMatrix_hessian_symmetric _ m
    (((contDiffAt_vectorProfileCellFirstVariation s₀ s₁ β t hβ ht i hi a hq hθ m hm).comp m
      (contDiffAt_const.prodMk contDiffAt_id)).of_le (by norm_num))

theorem vectorProfileCellSecondVariation_frobenius_source (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (hβ : 0<β) (ht : t<1) (i : ℕ) (hi : i≤k+1)
    (a : VectorProfileCellParameter n) (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1)))
    (hθ : a.2.1∈Ioo (0 : ℝ) 1) (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    deriv (fun q=>vectorProfileCellSecondVariation s₀ s₁ β t i (q,a.2) m) a.1+
      (1-t)/2*responseMatrixPair
        (vectorProfileCellHessianMatrix s₀ s₁ β t i a m*vectorProfileCellHessianMatrix s₀ s₁ β t i a m)
        (vectorProfileCellZMatrix s₀ s₁ β t i a m)=
      (1-t)*responseMatrixFrobeniusSquare
        (CFC.sqrt (vectorProfileCellHessianMatrix s₀ s₁ β t i a m)*
          vectorProfileCellBMatrix s₀ s₁ β t i a m*vectorProfileCellHessianMatrix s₀ s₁ β t i a m) := by
  rw [vectorProfileCellSecondVariation_generator s₀ s₁ β t hβ.ne' ht i hi a hq hθ m hm,
    response_second_variation_cfc_frobenius _ _
      (vectorProfileCellHessianMatrix_posDef s₀ s₁ β t hβ i a m hm).posSemidef
      (vectorProfileCellBMatrix_symmetric s₀ s₁ β t hβ.ne' ht i hi a hq hθ m hm)]

end QuantitativePaper
