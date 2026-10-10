module
public import QuantitativePaper.VectorProfileClosedRawFields
public import QuantitativePaper.VectorProfileRetainedExpectedContinuity
public import FourPapersCommon.RetainedExponentialNorm

@[expose] public section

/-! The true physical Hessian-square trace has a continuous retained
extension and a genuine closed-cell expected absolute-value envelope. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

def vectorProfileRetainedTraceSquare (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (q : ℝ) (z : VectorProfileParameter n×Field n) : ℝ:=
  β^2*euclideanOperatorTrace
    (hessianOperator (fun x=>vectorProfileCellJointPotential s₀ s₁ β t i ((q,z.1),x)) z.2*
     hessianOperator (fun x=>vectorProfileCellJointPotential s₀ s₁ β t i ((q,z.1),x)) z.2)

theorem retainedExponentialContinuousOn_vectorProfileRetainedTraceSquare
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (ht : t≤1) (i : ℕ) (hi : i≤k+1)
    (A B : ℝ) (hA : 0<A) (hB : B<1) :
    RetainedExponentialContinuousOn (vectorProfileRetainedTraceSquare (n:=n) s₀ s₁ β t i)
      (Icc (s₀.q i) (s₀.q (i+1))) (vectorProfileRetainedDomain n A B) := by
  have hH:=(retainedJetExponentialOn_vectorProfileCellRawHessian (n:=n)
    s₀ s₁ β t ht i hi A B hA hB).values
  exact ((hH.bilinear hH (ContinuousLinearMap.mul ℝ (Field n→L[ℝ]Field n))).compCLM euclideanOperatorTraceCLM).compCLM (β^2 • ContinuousLinearMap.id ℝ ℝ)

theorem vectorProfileRetainedTraceSquare_eq_physical
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0)
    (i : ℕ) (hi : i≤k+1) (q : ℝ) (hq : q∈Icc (s₀.q i) (s₀.q (i+1)))
    (z : VectorProfileParameter n×Field n) (hθ : z.1.1∈Icc (0:ℝ) 1) :
    let m:=vectorProfileCellJointGradient s₀ s₁ β t i ((q,z.1),z.2)
    vectorProfileRetainedTraceSquare s₀ s₁ β t i q z=
      Matrix.trace (vectorProfileCellHessianMatrix s₀ s₁ β t i (q,z.1) m*
        vectorProfileCellHessianMatrix s₀ s₁ β t i (q,z.1) m) := by
  dsimp only
  unfold vectorProfileCellHessianMatrix
  rw [vectorProfileCellPhysicalHessian_at_gradient s₀ s₁ β t hβ i hi (q,z.1) hq hθ z.2]
  simp only [euclideanOperatorMatrix_smul,Matrix.smul_mul,Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul]
  unfold vectorProfileRetainedTraceSquare euclideanOperatorTrace
  rw [euclideanOperatorMatrix_mul]
  ring

theorem continuousOn_vectorProfileRetainedTraceSquare_abs_expectation
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (ht : t≤1)
    (hθ : θ∈Ioo (0:ℝ) 1) (i : ℕ) (hi : i≤k+1) :
    ContinuousOn (vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht
      ⟨hθ.1.le,hθ.2.le⟩ (fun q z=>‖vectorProfileRetainedTraceSquare (n:=n) s₀ s₁ β t i q z‖))
      (Icc (s₀.q i) (s₀.q (i+1))) := by
  apply continuousOn_vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht
    ⟨hθ.1.le,hθ.2.le⟩ i hi (θ/2) ((θ+1)/2)
    (show θ∈Ioo (θ/2) ((θ+1)/2) from ⟨by linarith [hθ.1],by linarith [hθ.2]⟩)
  exact (retainedExponentialContinuousOn_vectorProfileRetainedTraceSquare (n:=n)
    s₀ s₁ β t ht i hi _ _ (by linarith [hθ.1]) (by linarith [hθ.2])).norm

end QuantitativePaper
