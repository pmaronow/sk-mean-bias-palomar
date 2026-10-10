module
public import QuantitativePaper.VectorProfileSecondVariationGrowth
public import FourPapersCommon.ExponentialTimePartial

@[expose] public section

/-! Actual curvature-pairing observables have exponential envelopes
for all joint derivatives on cropped strict cells. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2500000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem exponentialSmoothOn_vectorProfileCellFieldCurvaturePairing (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (l u a b : ℝ)
    (hl : s₀.q i≤l) (hu : u<s₀.q (i+1)) (ha : 0<a) (hb : b<1) :
    ExponentialSmoothOn (vectorProfileCellFieldCurvaturePairing (n:=n) s₀ s₁ β t i)
      (vectorProfileJointCylinder l u a b) := by
  have hU:=isOpen_vectorProfileJointCylinder (n:=n) l u a b
  have hRaw:=exponentialSmoothOn_vectorProfileCellJointPotential
    (n:=n) s₀ s₁ β t hβ ht i hi l u a b hu ha hb
  have hW:=exponentialSmoothOn_vectorProfileCellPotentialFirstVariation
    (n:=n) s₀ s₁ β t hβ ht i hi l u a b hu ha hb
  have hTime:=exponentialSmoothOn_vectorProfileCellPotentialTime
    (n:=n) s₀ s₁ β t hβ ht i hi l u a b hu ha hb
  have hInv:=exponentialSmoothOn_vectorProfileCellRawHessianInverse hn
    s₀ s₁ β t hβ ht i hi l u a b hl hu ha hb
  have hV:=hInv.bilinear (hTime.partialGradient hU) (ContinuousLinearMap.apply ℝ (Field n)).flip
  have hPair:=(hW.partialFDeriv hU).bilinear hV (ContinuousLinearMap.apply ℝ ℝ).flip
  have hFirst:=((hW.timePartial hU).sub hPair).compCLM
    ((2/((1-t)*β)) • ContinuousLinearMap.id ℝ ℝ)
  have hG:=hRaw.partialGradient hU
  have hSecond:=(hG.bilinear hG (innerSL ℝ)).compCLM
    ((β*(s₁.m i-s₀.m i)) • ContinuousLinearMap.id ℝ ℝ)
  apply (hFirst.add hSecond).congr
  intro z hz
  filter_upwards [hU.mem_nhds hz] with w hw
  have hq : w.1.1∈Ioo (s₀.q i) (s₀.q (i+1)):=
    ⟨hl.trans_lt hw.1.1,hw.1.2.trans hu⟩
  have hθ : w.1.2.1∈Ioo (0:ℝ) 1:=⟨ha.trans hw.2.1,hw.2.2.trans hb⟩
  have he:=vectorProfileCellFieldCurvaturePairing_formula s₀ s₁ β t hβ ht i hi w.1 hq hθ w.2
  change 2/((1-t)*β)*(deriv (fun q=>vectorProfileCellPotentialFirstVariation s₀ s₁ β t i (q,w.1.2) w.2) w.1.1-
    fderiv ℝ (vectorProfileCellPotentialFirstVariation s₀ s₁ β t i w.1) w.2
      ((Ring.inverse (hessianOperator (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i (w.1,y)) w.2))
        (gradient (vectorProfileCellPotentialTime s₀ s₁ β t i w.1) w.2)))+
      (β*(s₁.m i-s₀.m i))*inner ℝ
        (vectorProfileCellJointGradient s₀ s₁ β t i w)
        (vectorProfileCellJointGradient s₀ s₁ β t i w)=_
  rw [real_inner_self_eq_norm_sq]
  exact he.symm

end QuantitativePaper
