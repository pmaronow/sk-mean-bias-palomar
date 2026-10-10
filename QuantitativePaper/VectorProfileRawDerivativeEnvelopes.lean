module
public import QuantitativePaper.VectorProfileRawExponentialSmooth

@[expose] public section

/-! Actual profile first/second variations and the literal time partial
inherit the audited raw Gaussian joint exponential jet envelopes. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 1900000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem exponentialSmoothOn_vectorProfileCellPotentialFirstVariation
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (l u a b : ℝ)
    (hu : u<s₀.q (i+1)) (ha : 0<a) (hb : b<1) :
    ExponentialSmoothOn (fun z : VectorProfileCellParameter n×Field n=>
      vectorProfileCellPotentialFirstVariation s₀ s₁ β t i z.1 z.2)
      (vectorProfileJointCylinder l u a b) := by
  let f:=vectorProfileCellJointPotential (n:=n) s₀ s₁ β t i
  let U:=vectorProfileJointCylinder (n:=n) l u a b
  have hf:=exponentialSmoothOn_vectorProfileCellJointPotential (n:=n) s₀ s₁ β t hβ ht i hi l u a b hu ha hb
  apply (hf.directional (((0,(1,0)),0) : VectorProfileCellParameter n×Field n)).congr
  intro z hz
  filter_upwards [(isOpen_vectorProfileJointCylinder (n:=n) l u a b).mem_nhds hz] with w hw
  have hLine : HasDerivAt (fun θ : ℝ=>((w.1.1,θ,w.1.2.2),w.2)) ((0,(1,0)),0) w.1.2.1:=
    ((hasDerivAt_const w.1.2.1 w.1.1).prodMk
      ((hasDerivAt_id w.1.2.1).prodMk (hasDerivAt_const w.1.2.1 w.1.2.2))).prodMk
        (hasDerivAt_const w.1.2.1 w.2)
  exact (((hf.smooth w hw).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
    w.1.2.1 hLine).deriv.symm

theorem exponentialSmoothOn_vectorProfileCellPotentialSecondVariation
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (l u a b : ℝ)
    (hu : u<s₀.q (i+1)) (ha : 0<a) (hb : b<1) :
    ExponentialSmoothOn (fun z : VectorProfileCellParameter n×Field n=>
      vectorProfileCellPotentialSecondVariation s₀ s₁ β t i z.1 z.2)
      (vectorProfileJointCylinder l u a b) := by
  have hf:=exponentialSmoothOn_vectorProfileCellPotentialFirstVariation
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

theorem exponentialSmoothOn_vectorProfileCellPotentialTime
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (l u a b : ℝ)
    (hu : u<s₀.q (i+1)) (ha : 0<a) (hb : b<1) :
    ExponentialSmoothOn (fun z : VectorProfileCellParameter n×Field n=>
      vectorProfileCellPotentialTime s₀ s₁ β t i z.1 z.2)
      (vectorProfileJointCylinder l u a b) := by
  have hf:=exponentialSmoothOn_vectorProfileCellJointPotential
    (n:=n) s₀ s₁ β t hβ ht i hi l u a b hu ha hb
  apply (hf.directional (((1,(0,0)),0) : VectorProfileCellParameter n×Field n)).congr
  intro z hz
  filter_upwards [(isOpen_vectorProfileJointCylinder (n:=n) l u a b).mem_nhds hz] with w hw
  have hLine : HasDerivAt (fun q : ℝ=>((q,w.1.2),w.2)) ((1,(0,0)),0) w.1.1:=
    ((hasDerivAt_id w.1.1).prodMk (hasDerivAt_const w.1.1 w.1.2)).prodMk
      (hasDerivAt_const w.1.1 w.2)
  exact (((hf.smooth w hw).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
    w.1.1 hLine).deriv.symm

end QuantitativePaper
