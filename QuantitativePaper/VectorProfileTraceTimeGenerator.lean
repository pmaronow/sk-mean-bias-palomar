module
public import QuantitativePaper.VectorProfileHessianPositivity

@[expose] public section

/-! Genuine time differentiation of the trace reaction on strict cells.
The positive inverse-weight source uses the actual derivative at fixed m. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise MatrixOrder
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

def vectorProfileCellTraceTime (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (a : VectorProfileCellParameter n) (m : Field n) : ℝ:=
  deriv (fun q=>vectorProfileCellTrace s₀ s₁ β t i (q,a.2) m) a.1

def vectorProfileCellHessianTimeMatrix (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (a : VectorProfileCellParameter n) (m : Field n) : Matrix (Fin n) (Fin n) ℝ:=
  euclideanOperatorMatrix (deriv (fun q=>vectorProfileCellPhysicalHessian s₀ s₁ β t i (q,a.2) m) a.1)

theorem contDiffAt_vectorProfileCellTraceTime (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (i : ℕ) (hi : i ≤ k+1)
    (a : VectorProfileCellParameter n) (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1)))
    (hθ : a.2.1∈Ioo (0 : ℝ) 1) (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    ContDiffAt ℝ ∞ (fun z : VectorProfileCellParameter n×Field n=>
      vectorProfileCellTraceTime s₀ s₁ β t i z.1 z.2) (a,m) := by
  let U : ℝ×(VectorProfileParameter n×Field n)→ℝ:=
    fun z=>vectorProfileCellTrace s₀ s₁ β t i (z.1,z.2.1) z.2.2
  have hU : ContDiffAt ℝ ∞ U (a.1,a.2,m):=ContDiffAt.comp
    (f := fun z : ℝ×(VectorProfileParameter n×Field n)=>((z.1,z.2.1),z.2.2))
    (g := fun z : VectorProfileCellParameter n×Field n=>vectorProfileCellTrace s₀ s₁ β t i z.1 z.2)
    (a.1,a.2,m) (contDiffAt_vectorProfileCellTrace s₀ s₁ β t hβ ht i hi a hq hθ m hm) (by fun_prop)
  have hD:=contDiffAt_partialParamDerivative (1 : ℝ) U (a.1,a.2,m) hU
  have hh:=ContDiffAt.comp
    (f := fun z : VectorProfileCellParameter n×Field n=>(z.1.1,z.1.2,z.2))
    (g := partialParamDerivative (1 : ℝ) U) (a,m) hD (by fun_prop)
  simpa only [Function.comp_def,partialParamDerivative,fderiv_apply_one_eq_deriv,U,
    vectorProfileCellTraceTime] using hh

theorem vectorProfileCellHessianTimeMatrix_symmetric (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (i : ℕ) (hi : i ≤ k+1)
    (a : VectorProfileCellParameter n) (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1)))
    (hθ : a.2.1∈Ioo (0 : ℝ) 1) (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    (vectorProfileCellHessianTimeMatrix s₀ s₁ β t i a m).IsSymm := by
  unfold vectorProfileCellHessianTimeMatrix
  rw [(hasDerivAt_vectorProfileCellPhysicalHessian_time s₀ s₁ β t hβ ht i hi a hq hθ m hm).deriv]
  simp only [euclideanOperatorMatrix_smul,euclideanOperatorMatrix_mul,euclideanOperatorMatrix_add,
    euclideanOperatorMatrix_one]
  have hh:=vectorProfileCellHessianMatrix_symmetric s₀ s₁ β t hβ i a m hm
  dsimp only [vectorProfileCellHessianMatrix] at hh
  have hn:=euclideanOperatorMatrix_hessian_symmetric _ m
    (((contDiffAt_vectorProfileCellTrace s₀ s₁ β t hβ ht i hi a hq hθ m hm).comp m
      (contDiffAt_const.prodMk contDiffAt_id)).of_le (by norm_num))
  change (euclideanOperatorMatrix (vectorProfileCellTraceHessian s₀ s₁ β t i a m)).IsSymm at hn
  rw [Matrix.IsSymm,Matrix.transpose_smul,Matrix.transpose_mul,Matrix.transpose_mul,hh.eq,
    Matrix.transpose_add,hn.eq,Matrix.transpose_smul,Matrix.transpose_one]
  simp only [Matrix.mul_assoc]

theorem vectorProfileCellTraceTime_generator_raw (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (hβ : β≠0) (ht : t<1) (i : ℕ) (hi : i ≤ k+1)
    (a : VectorProfileCellParameter n) (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1)))
    (hθ : a.2.1∈Ioo (0 : ℝ) 1) (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    deriv (fun q=>vectorProfileCellTraceTime s₀ s₁ β t i (q,a.2) m) a.1+
      (1-t)/2*responseMatrixPair
        (vectorProfileCellHessianMatrix s₀ s₁ β t i a m*vectorProfileCellHessianMatrix s₀ s₁ β t i a m)
        (euclideanOperatorMatrix (hessianOperator (vectorProfileCellTraceTime s₀ s₁ β t i a) m))=
      -((1-t)/2)*responseMatrixPair
        (vectorProfileCellHessianTimeMatrix s₀ s₁ β t i a m*vectorProfileCellHessianMatrix s₀ s₁ β t i a m+
          vectorProfileCellHessianMatrix s₀ s₁ β t i a m*vectorProfileCellHessianTimeMatrix s₀ s₁ β t i a m)
        (euclideanOperatorMatrix (vectorProfileCellTraceHessian s₀ s₁ β t i a m)+
          (2*(β*vectorProfileMass s₀ s₁ a.2.1 i)) • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  let H : ℝ→Field n→L[ℝ]Field n:=fun q=>vectorProfileCellPhysicalHessian s₀ s₁ β t i (q,a.2) m
  let N : ℝ→Field n→L[ℝ]Field n:=fun q=>vectorProfileCellTraceHessian s₀ s₁ β t i (q,a.2) m
  let K : ℝ→Field n→L[ℝ]Field n:=fun q=>N q+
    (2*(β*vectorProfileMass s₀ s₁ a.2.1 i)) • (1 : Field n→L[ℝ]Field n)
  let D:=deriv H a.1
  let Ndot:=hessianOperator (vectorProfileCellTraceTime s₀ s₁ β t i a) m
  have hdH : HasDerivAt H D a.1:=
    (hasDerivAt_vectorProfileCellPhysicalHessian_time s₀ s₁ β t hβ ht i hi a hq hθ m hm).differentiableAt.hasDerivAt
  let U : ℝ×Field n→ℝ:=fun z=>vectorProfileCellTrace s₀ s₁ β t i (z.1,a.2) z.2
  have hU : ContDiffAt ℝ ∞ U (a.1,m):=ContDiffAt.comp
    (f := fun z : ℝ×Field n=>((z.1,a.2),z.2))
    (g := fun z : VectorProfileCellParameter n×Field n=>vectorProfileCellTrace s₀ s₁ β t i z.1 z.2)
    (a.1,m) (contDiffAt_vectorProfileCellTrace s₀ s₁ β t hβ ht i hi a hq hθ m hm) (by fun_prop)
  have hdN : HasDerivAt N Ndot a.1:=hasDerivAt_partial_hessian U a.1 m hU
  have hdK : HasDerivAt K Ndot a.1:=hdN.add_const _
  have hdF:=hasDerivAt_euclideanOperatorTrace ((hdH.mul hdH).mul hdK)
  simp only [Pi.mul_apply] at hdF
  have he : (fun q=>vectorProfileCellTraceTime s₀ s₁ β t i (q,a.2) m)=ᶠ[𝓝 a.1]
      (fun q=>-((1-t)/2)*euclideanOperatorTrace (H q*H q*K q)):=by
    filter_upwards [isOpen_Ioo.mem_nhds hq] with q hq'
    have hh:=hasDerivAt_vectorProfileCellPhysicalHessian_time s₀ s₁ β t hβ ht i hi (q,a.2) hq' hθ m hm
    unfold vectorProfileCellTraceTime vectorProfileCellTrace
    rw [(hasDerivAt_euclideanOperatorTrace hh).deriv]
    change euclideanOperatorTrace (-((1-t)/2) • (H q*K q*H q))=_
    simp only [euclideanOperatorTrace,euclideanOperatorMatrix_smul,euclideanOperatorMatrix_mul,
      Matrix.trace_smul,smul_eq_mul]
    congr 1
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle'
      (euclideanOperatorMatrix (H q)) (euclideanOperatorMatrix (K q)) (euclideanOperatorMatrix (H q))
  rw [he.deriv_eq,(hdF.const_mul (-((1-t)/2))).deriv]
  let h:=vectorProfileCellHessianMatrix s₀ s₁ β t i a m
  let d:=vectorProfileCellHessianTimeMatrix s₀ s₁ β t i a m
  let km:=euclideanOperatorMatrix (vectorProfileCellTraceHessian s₀ s₁ β t i a m)+
    (2*(β*vectorProfileMass s₀ s₁ a.2.1 i)) • (1 : Matrix (Fin n) (Fin n) ℝ)
  let nd:=euclideanOperatorMatrix Ndot
  have hdSym:=vectorProfileCellHessianTimeMatrix_symmetric s₀ s₁ β t hβ ht i hi a hq hθ m hm
  have hhSym:=vectorProfileCellHessianMatrix_symmetric s₀ s₁ β t hβ i a m hm
  have hsSym : (d*h+h*d).IsSymm:=by
    rw [Matrix.IsSymm,Matrix.transpose_add,Matrix.transpose_mul,Matrix.transpose_mul,hdSym.eq,hhSym.eq]
    exact add_comm _ _
  rw [responseMatrixPair_symm_left _ _ hsSym,responseMatrixPair_symm_left _ _
    (by rw [Matrix.IsSymm,Matrix.transpose_mul,hhSym.eq])]
  change -((1-t)/2)*euclideanOperatorTrace ((D*H a.1+H a.1*D)*K a.1+H a.1*H a.1*Ndot)+
    (1-t)/2*Matrix.trace (h*h*nd)= -((1-t)/2)*Matrix.trace ((d*h+h*d)*km)
  simp only [euclideanOperatorTrace,euclideanOperatorMatrix_add,euclideanOperatorMatrix_mul,
    Matrix.trace_add]
  simp only [K,N,euclideanOperatorMatrix_add,euclideanOperatorMatrix_smul,euclideanOperatorMatrix_one]
  change -((1-t)/2)*(Matrix.trace ((d*h+h*d)*km)+Matrix.trace (h*h*nd))+
    (1-t)/2*Matrix.trace (h*h*nd)= -((1-t)/2)*Matrix.trace ((d*h+h*d)*km)
  ring

theorem vectorProfileCellTraceTime_generator (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (hβ : 0<β) (ht : t<1) (i : ℕ) (hi : i ≤ k+1)
    (a : VectorProfileCellParameter n) (hq : a.1∈Ioo (s₀.q i) (s₀.q (i+1)))
    (hθ : a.2.1∈Ioo (0 : ℝ) 1) (m : Field n) (hm : m∈vectorOpenSpinCube n) :
    deriv (fun q=>vectorProfileCellTraceTime s₀ s₁ β t i (q,a.2) m) a.1+
      (1-t)/2*responseMatrixPair
        (vectorProfileCellHessianMatrix s₀ s₁ β t i a m*vectorProfileCellHessianMatrix s₀ s₁ β t i a m)
        (euclideanOperatorMatrix (hessianOperator (vectorProfileCellTraceTime s₀ s₁ β t i a) m))=
      2*responseMatrixFrobeniusSquare
        (CFC.sqrt ((vectorProfileCellHessianMatrix s₀ s₁ β t i a m)⁻¹)*
          vectorProfileCellHessianTimeMatrix s₀ s₁ β t i a m) := by
  rw [vectorProfileCellTraceTime_generator_raw s₀ s₁ β t hβ.ne' ht i hi a hq hθ m hm]
  apply response_generator_trace_time_cfc
    (vectorProfileCellHessianMatrix s₀ s₁ β t i a m) _
    (vectorProfileCellHessianTimeMatrix s₀ s₁ β t i a m)
    (vectorProfileCellHessianMatrix_posDef s₀ s₁ β t hβ i a m hm)
    (vectorProfileCellHessianTimeMatrix_symmetric s₀ s₁ β t hβ.ne' ht i hi a hq hθ m hm) (1-t)
  unfold vectorProfileCellHessianTimeMatrix
  rw [(hasDerivAt_vectorProfileCellPhysicalHessian_time s₀ s₁ β t hβ.ne' ht i hi a hq hθ m hm).deriv]
  simp only [euclideanOperatorMatrix_smul,euclideanOperatorMatrix_mul,euclideanOperatorMatrix_add,
    euclideanOperatorMatrix_one]
  rfl

end QuantitativePaper
