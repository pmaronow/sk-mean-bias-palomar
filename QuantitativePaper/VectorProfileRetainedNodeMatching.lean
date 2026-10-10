module
public import QuantitativePaper.VectorProfileClosedReaction
public import QuantitativePaper.VectorProfileResponseJumps

@[expose] public section

/-! Closed-node raw spatial jets agree exactly. Their trace-reaction
extensions have the literal mass jump, including repeated overlap nodes. -/
noncomputable section
open Set
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

theorem vectorProfileCell_potential_function_match
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (i j : ℕ) (hi : i≤k+1) (hj : j≤k+1)
    (a : VectorProfileCellParameter n) (hqi : a.1∈Icc (s₀.q i) (s₀.q (i+1)))
    (hqj : a.1∈Icc (s₀.q j) (s₀.q (j+1))) (hθ : a.2.1∈Icc (0:ℝ) 1) :
    (fun x : Field n=>vectorProfileCellJointPotential s₀ s₁ β t j (a,x))=
      (fun x : Field n=>vectorProfileCellJointPotential s₀ s₁ β t i (a,x)) := by
  rw [vectorProfileCellJointPotential_eq_scheme s₀ s₁ β t j hj a hqj hθ,
    vectorProfileCellJointPotential_eq_scheme s₀ s₁ β t i hi a hqi hθ]

theorem vectorProfileCell_raw_trace_function_match
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (i j : ℕ) (hi : i≤k+1) (hj : j≤k+1)
    (a : VectorProfileCellParameter n) (hqi : a.1∈Icc (s₀.q i) (s₀.q (i+1)))
    (hqj : a.1∈Icc (s₀.q j) (s₀.q (j+1))) (hθ : a.2.1∈Icc (0:ℝ) 1) :
    vectorProfileCellRawTrace (n:=n) s₀ s₁ β t j a=
      vectorProfileCellRawTrace s₀ s₁ β t i a := by
  funext x
  unfold vectorProfileCellRawTrace
  rw [vectorProfileCell_potential_function_match s₀ s₁ β t i j hi hj a hqi hqj hθ]

theorem vectorProfileRetainedTraceReaction_jump
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (i j : ℕ) (hi : i≤k+1) (hj : j≤k+1)
    (q : ℝ) (hqi : q∈Icc (s₀.q i) (s₀.q (i+1)))
    (hqj : q∈Icc (s₀.q j) (s₀.q (j+1)))
    (z : VectorProfileParameter n×Field n) (hθ : z.1.1∈Icc (0:ℝ) 1) :
    vectorProfileRetainedTraceReaction s₀ s₁ β t j q z-
      vectorProfileRetainedTraceReaction s₀ s₁ β t i q z=
      -(1-t)*β^3*(vectorProfileMass s₀ s₁ z.1.1 j-vectorProfileMass s₀ s₁ z.1.1 i)*
        euclideanOperatorTrace
          (hessianOperator (fun x=>vectorProfileCellJointPotential s₀ s₁ β t i ((q,z.1),x)) z.2*
           hessianOperator (fun x=>vectorProfileCellJointPotential s₀ s₁ β t i ((q,z.1),x)) z.2) := by
  unfold vectorProfileRetainedTraceReaction
  rw [vectorProfileCell_potential_function_match s₀ s₁ β t i j hi hj (q,z.1) hqi hqj hθ,
    vectorProfileCell_raw_trace_function_match s₀ s₁ β t i j hi hj (q,z.1) hqi hqj hθ]
  ring

end QuantitativePaper
