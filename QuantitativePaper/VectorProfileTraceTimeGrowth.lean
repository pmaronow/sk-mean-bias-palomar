module
public import QuantitativePaper.VectorProfileTraceTimePullback
public import QuantitativePaper.VectorProfileCurvaturePairingGrowth

@[expose] public section

/-! Actual fixed-magnetization trace time observables satisfy genuine
all-order exponential growth bounds in original field coordinates. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2500000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem exponentialSmoothOn_vectorProfileCellRawTrace
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (l u a b : ℝ)
    (hu : u<s₀.q (i+1)) (ha : 0<a) (hb : b<1) :
    ExponentialSmoothOn (fun z : VectorProfileCellParameter n×Field n=>
      vectorProfileCellRawTrace s₀ s₁ β t i z.1 z.2)
      (vectorProfileJointCylinder l u a b) := by
  have hf:=exponentialSmoothOn_vectorProfileCellJointPotential
    (n:=n) s₀ s₁ β t hβ ht i hi l u a b hu ha hb
  exact (hf.partialHessian (isOpen_vectorProfileJointCylinder l u a b)).compCLM euclideanOperatorTraceCLM

theorem exponentialSmoothOn_vectorProfileCellFieldTraceTime (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (l u a b : ℝ)
    (hl : s₀.q i≤l) (hu : u<s₀.q (i+1)) (ha : 0<a) (hb : b<1) :
    ExponentialSmoothOn (vectorProfileCellFieldTraceTime (n:=n) s₀ s₁ β t i)
      (vectorProfileJointCylinder l u a b) := by
  have hU:=isOpen_vectorProfileJointCylinder (n:=n) l u a b
  have hTrace:=exponentialSmoothOn_vectorProfileCellRawTrace
    (n:=n) s₀ s₁ β t hβ ht i hi l u a b hu ha hb
  have hTime:=exponentialSmoothOn_vectorProfileCellPotentialTime
    (n:=n) s₀ s₁ β t hβ ht i hi l u a b hu ha hb
  have hInv:=exponentialSmoothOn_vectorProfileCellRawHessianInverse hn
    s₀ s₁ β t hβ ht i hi l u a b hl hu ha hb
  have hV:=hInv.bilinear (hTime.partialGradient hU) (ContinuousLinearMap.apply ℝ (Field n)).flip
  have hPair:=(hTrace.partialFDeriv hU).bilinear hV (ContinuousLinearMap.apply ℝ ℝ).flip
  apply (((hTrace.timePartial hU).sub hPair).compCLM (β • ContinuousLinearMap.id ℝ ℝ)).congr
  intro z hz
  filter_upwards [hU.mem_nhds hz] with w hw
  have hq : w.1.1∈Ioo (s₀.q i) (s₀.q (i+1)):=
    ⟨hl.trans_lt hw.1.1,hw.1.2.trans hu⟩
  have hθ : w.1.2.1∈Ioo (0:ℝ) 1:=⟨ha.trans hw.2.1,hw.2.2.trans hb⟩
  exact (vectorProfileCellFieldTraceTime_formula s₀ s₁ β t hβ ht i hi w.1 hq hθ w.2).symm

end QuantitativePaper
