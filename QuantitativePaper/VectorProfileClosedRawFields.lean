module
public import QuantitativePaper.VectorProfileClosedRawJets
public import QuantitativePaper.VectorProfileRawTraceCheckpoint
public import FourPapersCommon.RetainedExponentialContinuous

@[expose] public section

/-! The true retained trace and profile/spatial derivative fields have
continuous, exponentially bounded values through closed cell endpoints. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

theorem retainedJetExponentialOn_vectorProfileCellVariationGradient
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (ht : t≤1) (i : ℕ) (hi : i≤k+1)
    (A B : ℝ) (hA : 0<A) (hB : B<1) :
    RetainedJetExponentialOn (fun (q : ℝ) (z : VectorProfileParameter n×Field n)=>
      gradient (vectorProfileCellPotentialFirstVariation s₀ s₁ β t i (q,z.1)) z.2)
      (Icc (s₀.q i) (s₀.q (i+1))) (vectorProfileRetainedDomain n A B) :=
  (retainedJetExponentialOn_vectorProfileCellPotentialFirstVariation (n:=n)
    s₀ s₁ β t ht i hi A B hA hB).partialGradient (isOpen_vectorProfileRetainedDomain A B)

theorem retainedJetExponentialOn_vectorProfileCellRawTrace
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (ht : t≤1) (i : ℕ) (hi : i≤k+1)
    (A B : ℝ) (hA : 0<A) (hB : B<1) :
    RetainedJetExponentialOn (fun (q : ℝ) (z : VectorProfileParameter n×Field n)=>
      vectorProfileCellRawTrace s₀ s₁ β t i (q,z.1) z.2)
      (Icc (s₀.q i) (s₀.q (i+1))) (vectorProfileRetainedDomain n A B) :=
  (retainedJetExponentialOn_vectorProfileCellRawHessian (n:=n)
    s₀ s₁ β t ht i hi A B hA hB).compCLM euclideanOperatorTraceCLM

theorem retainedJetExponentialOn_vectorProfileCellRawTraceProfile
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (ht : t≤1) (i : ℕ) (hi : i≤k+1)
    (A B : ℝ) (hA : 0<A) (hB : B<1) :
    RetainedJetExponentialOn (fun (q : ℝ) (z : VectorProfileParameter n×Field n)=>
      deriv (fun θ=>vectorProfileCellRawTrace s₀ s₁ β t i (q,θ,z.1.2) z.2) z.1.1)
      (Icc (s₀.q i) (s₀.q (i+1))) (vectorProfileRetainedDomain n A B) := by
  have hf:=retainedJetExponentialOn_vectorProfileCellRawTrace (n:=n) s₀ s₁ β t ht i hi A B hA hB
  apply (hf.directional (((1,0),0) : VectorProfileParameter n×Field n)).congr
  intro q hq z hz
  filter_upwards [(isOpen_vectorProfileRetainedDomain (n:=n) A B).mem_nhds hz] with w hw
  have hd:=((hf.smooth q hq w hw).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt w.1.1
    (((hasDerivAt_id w.1.1).prodMk (hasDerivAt_const w.1.1 w.1.2)).prodMk
      (hasDerivAt_const w.1.1 w.2))
  exact hd.deriv.symm

theorem retainedJetExponentialOn_vectorProfileCellRawTraceFDeriv
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (ht : t≤1) (i : ℕ) (hi : i≤k+1)
    (A B : ℝ) (hA : 0<A) (hB : B<1) :
    RetainedJetExponentialOn (fun (q : ℝ) (z : VectorProfileParameter n×Field n)=>
      fderiv ℝ (vectorProfileCellRawTrace s₀ s₁ β t i (q,z.1)) z.2)
      (Icc (s₀.q i) (s₀.q (i+1))) (vectorProfileRetainedDomain n A B) :=
  (retainedJetExponentialOn_vectorProfileCellRawTrace (n:=n) s₀ s₁ β t ht i hi A B hA hB).partialFDeriv (isOpen_vectorProfileRetainedDomain A B)

theorem retainedJetExponentialOn_vectorProfileCellRawTraceGradient
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (ht : t≤1) (i : ℕ) (hi : i≤k+1)
    (A B : ℝ) (hA : 0<A) (hB : B<1) :
    RetainedJetExponentialOn (fun (q : ℝ) (z : VectorProfileParameter n×Field n)=>
      gradient (vectorProfileCellRawTrace s₀ s₁ β t i (q,z.1)) z.2)
      (Icc (s₀.q i) (s₀.q (i+1))) (vectorProfileRetainedDomain n A B) :=
  (retainedJetExponentialOn_vectorProfileCellRawTrace (n:=n) s₀ s₁ β t ht i hi A B hA hB).partialGradient (isOpen_vectorProfileRetainedDomain A B)

theorem retainedJetExponentialOn_vectorProfileCellRawTraceHessian
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (ht : t≤1) (i : ℕ) (hi : i≤k+1)
    (A B : ℝ) (hA : 0<A) (hB : B<1) :
    RetainedJetExponentialOn (fun (q : ℝ) (z : VectorProfileParameter n×Field n)=>
      hessianOperator (vectorProfileCellRawTrace s₀ s₁ β t i (q,z.1)) z.2)
      (Icc (s₀.q i) (s₀.q (i+1))) (vectorProfileRetainedDomain n A B) :=
  (retainedJetExponentialOn_vectorProfileCellRawTrace (n:=n) s₀ s₁ β t ht i hi A B hA hB).partialHessian (isOpen_vectorProfileRetainedDomain A B)

end QuantitativePaper
