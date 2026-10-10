module
public import FourPapersCommon.FiniteStateCascadeResponses

@[expose] public section

/-! A rank-one Gaussian direction has exactly its single binary-coordinate
Hessian/gradient-square response under the actual normalized future kernel. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace FourPapersCommon
open OverlapPaper SpinGlass.AT
variable {S I : Type*} [Fintype S] [Fintype I] [DecidableEq I]
  [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
local instance : ContinuousSMul ℝ (FiniteStateField S) :=
  PolynormableSpace.continuousSMul ℝ (FiniteStateField S)

theorem finiteStateCascadeCovarianceResponse_rank_one (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (j q : ℕ) (H K : FiniteStateField S) (i : I) (r : ℝ) :
    finiteStateCascadeCovarianceResponse V a L j q H
      (r • (EuclideanSpace.proj i : FiniteStateGaussianInput I→L[ℝ]ℝ).smulRight K)=
      r^2*sourceKernelExpectation
        (fun p=>finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (j+p)) q
        (fun y=>fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) y K K+
          a j*(fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) y K)^2) H := by
  classical
  let Q : ℕ→Kernel (FiniteStateField S) (FiniteStateField S):=fun p=>finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (j+p)
  let U:=finiteStateGaussianTerminalCascade V a L j
  have hA (l : I) : (r • (EuclideanSpace.proj i : FiniteStateGaussianInput I→L[ℝ]ℝ).smulRight K) (EuclideanSpace.single l 1)=
      if l=i then r • K else 0 := by
    by_cases hl:l=i
    · subst l
      simp only [ite_true,ContinuousLinearMap.smul_apply,ContinuousLinearMap.smulRight_apply]
      change r • ((EuclideanSpace.single i 1 : FiniteStateGaussianInput I) i • K)=r • K
      simp
    · simp only [if_neg hl,ContinuousLinearMap.smul_apply,ContinuousLinearMap.smulRight_apply]
      change r • ((EuclideanSpace.single l 1 : FiniteStateGaussianInput I) i • K)=0
      simp [EuclideanSpace.single_apply,Ne.symm hl]
  have hz : sourceKernelExpectation Q q (fun _=>0) H=0 := by
    simpa only [zero_mul] using sourceKernelExpectation_const_mul Q (fun _=>0) 0 q H
  unfold finiteStateCascadeCovarianceResponse
  simp_rw [hA]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true,map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
    have he : (fun y=>r*(r*fderiv ℝ (fderiv ℝ U) y K K)+
        a j*(r*fderiv ℝ U y K)*(r*fderiv ℝ U y K))=
        fun y=>r^2*(fderiv ℝ (fderiv ℝ U) y K K+a j*(fderiv ℝ U y K)^2) := by
      funext y;ring
    change sourceKernelExpectation Q q _ H=_
    rw [he,sourceKernelExpectation_const_mul]
  · intro l _ hli
    simp only [if_neg hli,map_zero,mul_zero,zero_mul,add_zero]
    exact hz
  · simp

end FourPapersCommon
