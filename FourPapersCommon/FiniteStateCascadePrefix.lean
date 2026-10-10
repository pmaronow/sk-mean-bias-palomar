module
public import FourPapersCommon.FiniteStateCascadeResponses
public import OverlapPaper.ReplicaSourceGroupedMoments

@[expose] public section

/-! Finite-prefix invariance of genuine Gaussian cascades and their covariance
responses. No arbitrary choices beyond the levels used by the cascade affect
its value or its actual normalized probability expectations. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Real
open scoped BigOperators
namespace FourPapersCommon
open OverlapPaper SpinGlass.AT
set_option maxHeartbeats 1400000
variable {S I : Type*} [Fintype S] [Fintype I]

theorem finiteStateGaussianTerminalCascade_congr_prefix
    (V : S→ℝ) (a b : ℕ→ℝ)
    (L M : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (J : ℕ)
    (hm : ∀j<J,a j=b j) (hL : ∀j<J,L j=M j) :
    finiteStateGaussianTerminalCascade V a L J=finiteStateGaussianTerminalCascade V b M J := by
  induction J with
  | zero => rfl
  | succ J ih =>
    change finiteStateGaussianStep (a J) (L J) (finiteStateGaussianTerminalCascade V a L J)=
      finiteStateGaussianStep (b J) (M J) (finiteStateGaussianTerminalCascade V b M J)
    rw [hm J (by omega),hL J (by omega),ih (fun j hj=>hm j (by omega)) (fun j hj=>hL j (by omega))]

 theorem finiteStateGaussianCascadeKernel_congr_prefix
    (V : S→ℝ) (a b : ℕ→ℝ)
    (L M : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (J : ℕ)
    (hm : ∀j<J+1,a j=b j) (hL : ∀j<J+1,L j=M j) :
    finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) J=
      finiteStateGaussianCascadeKernel b M (gtStateLogPartition V) J := by
  change finiteStateGaussianStepKernel (a J) (L J) (finiteStateGaussianTerminalCascade V a L J)=
      finiteStateGaussianStepKernel (b J) (M J) (finiteStateGaussianTerminalCascade V b M J)
  rw [hm J (by omega),hL J (by omega),finiteStateGaussianTerminalCascade_congr_prefix V a b L M J
    (fun j hj=>hm j (by omega)) (fun j hj=>hL j (by omega))]

variable {D : Type*} [Fintype D] [DecidableEq D]

theorem finiteStateCascadeCovarianceResponse_congr_prefix
    (V : S→ℝ) (a b : ℕ→ℝ)
    (L M : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (j q : ℕ) (hq : 0<q)
    (hm : ∀i<j+q,a i=b i) (hL : ∀i<j+q,L i=M i) (H : FiniteStateField S)
    (A : FiniteStateGaussianInput D→L[ℝ]FiniteStateField S) :
    finiteStateCascadeCovarianceResponse V a L j q H A=
      finiteStateCascadeCovarianceResponse V b M j q H A := by
  have hU:=finiteStateGaussianTerminalCascade_congr_prefix V a b L M j
    (fun i hi=>hm i (by omega)) (fun i hi=>hL i (by omega))
  unfold finiteStateCascadeCovarianceResponse
  apply Finset.sum_congr rfl
  intro i _
  rw [hU,hm j (by omega)]
  apply sourceKernelExpectation_congr_kernels
  intro r hr
  exact finiteStateGaussianCascadeKernel_congr_prefix V a b L M (j+r)
    (fun i hi=>hm i (by omega)) (fun i hi=>hL i (by omega))

end FourPapersCommon
