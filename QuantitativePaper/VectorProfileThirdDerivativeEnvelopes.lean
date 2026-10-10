module
public import QuantitativePaper.VectorProfileThirdLinearizedPDE
public import QuantitativePaper.VectorProfileClosedRawJets
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

theorem exponentialSmoothOn_vectorProfileCellPotentialThirdVariation
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (l u a b : ℝ)
    (hu : u<s₀.q (i+1)) (ha : 0<a) (hb : b<1) :
    ExponentialSmoothOn (fun z : VectorProfileCellParameter n×Field n=>
      vectorProfileCellPotentialThirdVariation s₀ s₁ β t i z.1 z.2)
      (vectorProfileJointCylinder l u a b) := by
  have hf:=exponentialSmoothOn_vectorProfileCellPotentialSecondVariation
    (n:=n) s₀ s₁ β t hβ ht i hi l u a b hu ha hb
  apply (hf.directional (((0,(1,0)),0) : VectorProfileCellParameter n×Field n)).congr
  intro z hz
  filter_upwards [(isOpen_vectorProfileJointCylinder (n:=n) l u a b).mem_nhds hz] with w hw
  have hLine : HasDerivAt (fun θ : ℝ=>((w.1.1,θ,w.1.2.2),w.2)) ((0,(1,0)),0) w.1.2.1:=
    ((hasDerivAt_const w.1.2.1 w.1.1).prodMk
      ((hasDerivAt_id w.1.2.1).prodMk (hasDerivAt_const w.1.2.1 w.1.2.2))).prodMk
        (hasDerivAt_const w.1.2.1 w.2)
  exact (((hf.smooth w hw).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
    w.1.2.1 hLine).deriv.symm

theorem retainedJetExponentialOn_vectorProfileCellPotentialThirdVariation
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (ht : t≤1) (i : ℕ) (hi : i≤k+1)
    (A B : ℝ) (hA : 0<A) (hB : B<1) :
    RetainedJetExponentialOn (fun (q : ℝ) (z : VectorProfileParameter n×Field n)=>
      vectorProfileCellPotentialThirdVariation s₀ s₁ β t i (q,z.1) z.2)
      (Icc (s₀.q i) (s₀.q (i+1))) (vectorProfileRetainedDomain n A B) := by
  have hf:=retainedJetExponentialOn_vectorProfileCellPotentialSecondVariation (n:=n) s₀ s₁ β t ht i hi A B hA hB
  apply (hf.directional (((1,0),0) : VectorProfileParameter n×Field n)).congr
  intro q hq z hz
  filter_upwards [(isOpen_vectorProfileRetainedDomain (n:=n) A B).mem_nhds hz] with w hw
  have hd:=((hf.smooth q hq w hw).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt w.1.1
    (((hasDerivAt_id w.1.1).prodMk (hasDerivAt_const w.1.1 w.1.2)).prodMk
      (hasDerivAt_const w.1.1 w.2))
  exact hd.deriv.symm

end QuantitativePaper
