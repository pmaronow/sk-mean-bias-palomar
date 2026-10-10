module
public import QuantitativePaper.VectorProfileRetainedIntegrable
public import QuantitativePaper.VectorProfileClosedRawFields

@[expose] public section

/-! Actual physical Hessian trace on closed profile cells. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

def vectorProfileRetainedPhysicalTrace (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ)
    (q : ℝ) (z : VectorProfileParameter n×Field n) : ℝ:=
  β*vectorProfileCellRawTrace s₀ s₁ β t i (q,z.1) z.2

theorem retainedExponentialContinuousOn_vectorProfileRetainedPhysicalTrace
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (ht : t≤1) (i : ℕ) (hi : i≤k+1)
    (A B : ℝ) (hA : 0<A) (hB : B<1) :
    RetainedExponentialContinuousOn (vectorProfileRetainedPhysicalTrace (n:=n) s₀ s₁ β t i)
      (Icc (s₀.q i) (s₀.q (i+1))) (vectorProfileRetainedDomain n A B) := by
  exact (retainedJetExponentialOn_vectorProfileCellRawTrace (n:=n) s₀ s₁ β t ht i hi A B hA hB).values.compCLM (β •ContinuousLinearMap.id ℝ ℝ)

theorem vectorProfileRetainedPhysicalTrace_eq_physical
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0)
    (i : ℕ) (hi : i≤k+1) (q : ℝ) (hq : q∈Icc (s₀.q i) (s₀.q (i+1)))
    (z : VectorProfileParameter n×Field n) (hθ : z.1.1∈Icc (0:ℝ) 1) :
    let m:=vectorProfileCellJointGradient s₀ s₁ β t i ((q,z.1),z.2)
    vectorProfileRetainedPhysicalTrace s₀ s₁ β t i q z=
      Matrix.trace (vectorProfileCellHessianMatrix s₀ s₁ β t i (q,z.1) m) := by
  dsimp only
  unfold vectorProfileCellHessianMatrix
  rw [vectorProfileCellPhysicalHessian_at_gradient s₀ s₁ β t hβ i hi (q,z.1) hq hθ z.2]
  simp only [euclideanOperatorMatrix_smul,Matrix.trace_smul,smul_eq_mul]
  rfl

theorem integrable_vectorProfile_retained_physical_trace
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (ht : t≤1)
    (i : ℕ) (hi : i≤k+1) (hθ : θ∈Ioo (0:ℝ) 1)
    (q : NNReal) (hq : (q:ℝ)∈Icc (s₀.q i) (s₀.q (i+1))) :
    Integrable (fun sample : VectorDisorderBrownianSample n=>
      vectorProfileRetainedPhysicalTrace s₀ s₁ β t i q
        ((θ,sample.1),vectorFiniteState (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩) β t ht q sample))
      (vectorFiniteDisorderTilt (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩) β t outer) := by
  exact integrable_vectorProfile_retained_observable s₀ s₁ β t outer θ ht ⟨hθ.1.le,hθ.2.le⟩ i hi
    (θ/2) ((θ+1)/2) ⟨by linarith [hθ.1],by linarith [hθ.2]⟩ _
    (retainedExponentialContinuousOn_vectorProfileRetainedPhysicalTrace s₀ s₁ β t ht i hi
      _ _ (by linarith [hθ.1]) (by linarith [hθ.2])) q hq

theorem continuousOn_vectorProfileRetainedPhysicalTrace_expectation
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (ht : t≤1)
    (hθ : θ∈Ioo (0:ℝ) 1) (i : ℕ) (hi : i≤k+1) :
    ContinuousOn (vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht
      ⟨hθ.1.le,hθ.2.le⟩ (vectorProfileRetainedPhysicalTrace (n:=n) s₀ s₁ β t i))
      (Icc (s₀.q i) (s₀.q (i+1))) := by
  apply continuousOn_vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht
    ⟨hθ.1.le,hθ.2.le⟩ i hi (θ/2) ((θ+1)/2)
    (show θ∈Ioo (θ/2) ((θ+1)/2) from ⟨by linarith [hθ.1],by linarith [hθ.2]⟩)
  exact retainedExponentialContinuousOn_vectorProfileRetainedPhysicalTrace (n:=n)
    s₀ s₁ β t ht i hi _ _ (by linarith [hθ.1]) (by linarith [hθ.2])

end QuantitativePaper
