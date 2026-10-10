module
public import FourPapersCommon.RetainedJetBounds
public import QuantitativePaper.VectorProfileTailClosedContinuity
public import QuantitativePaper.VectorProfileRawDerivativeEnvelopes

@[expose] public section

/-! Genuine raw retained derivative fields, with continuous values and
uniform exponential envelopes on closed overlap cells. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def vectorProfileRetainedDomain (n : ℕ) (A B : ℝ) : Set (VectorProfileParameter n×Field n):=
  {z | z.1.1∈Ioo A B}

theorem isOpen_vectorProfileRetainedDomain (A B : ℝ) :
    IsOpen (vectorProfileRetainedDomain n A B):=
  isOpen_Ioo.preimage (by fun_prop)

theorem retainedJetExponentialOn_vectorProfileCellJointPotential
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (ht : t≤1) (i : ℕ) (hi : i≤k+1)
    (A B : ℝ) (hA : 0<A) (hB : B<1) :
    RetainedJetExponentialOn (fun (q : ℝ) (z : VectorProfileParameter n×Field n)=>
      vectorProfileCellJointPotential s₀ s₁ β t i ((q,z.1),z.2))
      (Icc (s₀.q i) (s₀.q (i+1))) (vectorProfileRetainedDomain n A B) := by
  let F : ℝ→ℝ×VectorParameter n→ℝ:=fun q y=>
    vectorProfileTailRecursion s₀ s₁ β t q y.1 y.2.1 (k+2) y.2.2
  let V : Set (ℝ×VectorParameter n):={y | y.1∈Ioo A B}
  have hF : RetainedJetExponentialOn F (Icc (s₀.q i) (s₀.q (i+1))) V:=by
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro q hq y hy
      exact contDiffAt_vectorProfileTailRecursion_joint s₀ s₁ β t q ht
        ⟨(s₀.q_nonneg (by omega)).trans hq.1,hq.2.trans (s₀.q_le_one (by omega))⟩
        (k+2) le_rfl y ⟨hA.trans hy.1,hy.2.trans hB⟩
    · intro r
      exact (continuousOn_vectorProfileTailRecursion_retained_jets s₀ s₁ β t ht i hi r).mono
        (fun w hw=>⟨hw.1,⟨hA.trans hw.2.1,hw.2.2.trans hB⟩⟩)
    · intro r
      obtain ⟨C,R,hC,hR,hjets⟩:=exists_vectorProfileTailRecursion_closed_retained_exp_jets
        (n:=n) s₀ s₁ β t ht i r hi A B hA hB
      exact ⟨C,R,zero_le_one.trans hC,hR,fun q hq y hy=>hjets r le_rfl q hq y hy⟩
  let L:=LinearIsometryEquiv.prodAssoc ℝ ℝ (Couplings n×ℝ) (Field n)
  have hL : ∀z∈vectorProfileRetainedDomain n A B,L z∈V:=fun _ hz=>hz
  apply (hF.precompIsometry L _ hL).congr
  intro q hq z hz
  filter_upwards [(isOpen_vectorProfileRetainedDomain (n:=n) A B).mem_nhds hz] with w hw
  exact (vectorProfilePhysicalCell_eq_tail s₀ s₁ β t i hi q w.1.1
    ⟨(hA.trans hw.1).le,(hw.2.trans hB).le⟩ hq w.1.2 w.2).symm

theorem retainedJetExponentialOn_vectorProfileCellPotentialFirstVariation
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (ht : t≤1) (i : ℕ) (hi : i≤k+1)
    (A B : ℝ) (hA : 0<A) (hB : B<1) :
    RetainedJetExponentialOn (fun (q : ℝ) (z : VectorProfileParameter n×Field n)=>
      vectorProfileCellPotentialFirstVariation s₀ s₁ β t i (q,z.1) z.2)
      (Icc (s₀.q i) (s₀.q (i+1))) (vectorProfileRetainedDomain n A B) := by
  have hf:=retainedJetExponentialOn_vectorProfileCellJointPotential (n:=n) s₀ s₁ β t ht i hi A B hA hB
  apply (hf.directional (((1,0),0) : VectorProfileParameter n×Field n)).congr
  intro q hq z hz
  filter_upwards [(isOpen_vectorProfileRetainedDomain (n:=n) A B).mem_nhds hz] with w hw
  have hd:=((hf.smooth q hq w hw).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt w.1.1
    (((hasDerivAt_id w.1.1).prodMk (hasDerivAt_const w.1.1 w.1.2)).prodMk
      (hasDerivAt_const w.1.1 w.2))
  exact hd.deriv.symm

theorem retainedJetExponentialOn_vectorProfileCellPotentialSecondVariation
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (ht : t≤1) (i : ℕ) (hi : i≤k+1)
    (A B : ℝ) (hA : 0<A) (hB : B<1) :
    RetainedJetExponentialOn (fun (q : ℝ) (z : VectorProfileParameter n×Field n)=>
      vectorProfileCellPotentialSecondVariation s₀ s₁ β t i (q,z.1) z.2)
      (Icc (s₀.q i) (s₀.q (i+1))) (vectorProfileRetainedDomain n A B) := by
  have hf:=retainedJetExponentialOn_vectorProfileCellPotentialFirstVariation (n:=n) s₀ s₁ β t ht i hi A B hA hB
  apply (hf.directional (((1,0),0) : VectorProfileParameter n×Field n)).congr
  intro q hq z hz
  filter_upwards [(isOpen_vectorProfileRetainedDomain (n:=n) A B).mem_nhds hz] with w hw
  have hd:=((hf.smooth q hq w hw).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt w.1.1
    (((hasDerivAt_id w.1.1).prodMk (hasDerivAt_const w.1.1 w.1.2)).prodMk
      (hasDerivAt_const w.1.1 w.2))
  exact hd.deriv.symm

theorem retainedJetExponentialOn_vectorProfileCellRawHessian
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (ht : t≤1) (i : ℕ) (hi : i≤k+1)
    (A B : ℝ) (hA : 0<A) (hB : B<1) :
    RetainedJetExponentialOn (fun (q : ℝ) (z : VectorProfileParameter n×Field n)=>
      hessianOperator (fun x=>vectorProfileCellJointPotential s₀ s₁ β t i ((q,z.1),x)) z.2)
      (Icc (s₀.q i) (s₀.q (i+1))) (vectorProfileRetainedDomain n A B) :=
  (retainedJetExponentialOn_vectorProfileCellJointPotential (n:=n) s₀ s₁ β t ht i hi A B hA hB).partialHessian
    (isOpen_vectorProfileRetainedDomain A B)

end QuantitativePaper
