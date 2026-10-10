module
public import QuantitativePaper.VectorProfileInverseExponentialSmooth
public import QuantitativePaper.VectorProfileRawDerivativeEnvelopes

@[expose] public section

/-! The actual second Legendre variation in original field coordinates
has genuine exponential envelopes for every derivative on cropped cells. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2300000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem exponentialSmoothOn_vectorProfileCellFieldSecondVariation (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (l u a b : ℝ)
    (hl : s₀.q i≤l) (hu : u<s₀.q (i+1)) (ha : 0<a) (hb : b<1) :
    ExponentialSmoothOn (vectorProfileCellFieldSecondVariation (n:=n) s₀ s₁ β t i)
      (vectorProfileJointCylinder l u a b) := by
  let U:=vectorProfileJointCylinder (n:=n) l u a b
  have hU:=isOpen_vectorProfileJointCylinder (n:=n) l u a b
  have hW:=exponentialSmoothOn_vectorProfileCellPotentialFirstVariation
    (n:=n) s₀ s₁ β t hβ ht i hi l u a b hu ha hb
  have hZ:=exponentialSmoothOn_vectorProfileCellPotentialSecondVariation
    (n:=n) s₀ s₁ β t hβ ht i hi l u a b hu ha hb
  have hG:=hW.partialGradient hU
  have hInv:=exponentialSmoothOn_vectorProfileCellRawHessianInverse hn
    s₀ s₁ β t hβ ht i hi l u a b hl hu ha hb
  have hV:=hInv.bilinear hG (ContinuousLinearMap.apply ℝ (Field n)).flip
  have hInner:=hG.bilinear hV (innerSL ℝ)
  have hFormula:=(hZ.neg.add hInner).compCLM (β⁻¹ • ContinuousLinearMap.id ℝ ℝ)
  apply hFormula.congr
  intro z hz
  filter_upwards [hU.mem_nhds hz] with w hw
  have hq : w.1.1∈Ioo (s₀.q i) (s₀.q (i+1)):=
    ⟨hl.trans_lt hw.1.1,hw.1.2.trans hu⟩
  have hθ : w.1.2.1∈Ioo (0:ℝ) 1:=⟨ha.trans hw.2.1,hw.2.2.trans hb⟩
  exact (vectorProfileCellSecondVariation_pullback s₀ s₁ β t hβ ht i hi w.1 hq hθ w.2).symm

end QuantitativePaper
