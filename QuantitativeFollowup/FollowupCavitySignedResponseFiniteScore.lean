module
public import FourPapersCommon.FiniteStateCascadePosteriorJets

@[expose] public section

/-! The initial-field score of the honest retained finite Gaussian
posterior. This is a derivative of its actual normalized log density. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper OverlapPaper
open scoped NNReal Topology BigOperators ContDiff
namespace QuantitativeFollowup
variable {S : Type} [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1800000

def cavityFinitePosteriorScore (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (N : ℕ)
    (H K : FiniteStateField S) (z : (Fin (N+1)→Field n)×S) : ℝ :=
  K z.2-∑i,cascadePosteriorStieltjesWeight a N i*
    fderiv ℝ (cascadePosteriorStieltjesPotential V a L N z.1 i) H K

theorem fderiv_cascadePosteriorLogDensity_stieltjes (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (N : ℕ)
    (H K : FiniteStateField S) (z : (Fin (N+1)→Field n)×S) :
    fderiv ℝ (fun Q=>cascadePosteriorLogDensity V a L (N+1) Q z) H K =
      cavityFinitePosteriorScore V a L N H K z := by
  let w := cascadePosteriorHistory L (N+1) 0 z.1 (Fin.last (N+1))
  let U := cascadePosteriorStieltjesPotential V a L N z.1
  have hu (i : Option (Option (Fin N))) : ContDiff ℝ ∞ (U i) := by
    cases i with
    | none=>
      dsimp only [U,cascadePosteriorStieltjesPotential]
      rw [cascadePosteriorHistoryPotential_eq_translate]
      exact (contDiff_finiteStateGaussianTerminalCascade V a ha L _).comp
        (contDiff_id.add contDiff_const)
    | some i=>
      cases i <;> dsimp only [U,cascadePosteriorStieltjesPotential] <;>
        rw [cascadePosteriorHistoryPotential_eq_translate] <;>
        exact (contDiff_finiteStateGaussianTerminalCascade V a ha L _).comp
          (contDiff_id.add contDiff_const)
  have ht : (fun Q : FiniteStateField S=>V z.2+(Q+w) z.2)=
      fun Q=>V z.2+w z.2+(EuclideanSpace.proj z.2 : FiniteStateField S→L[ℝ]ℝ) Q := by
    funext Q
    simp only [EuclideanSpace.coe_proj,PiLp.add_apply]
    ring
  have hd : (fun Q=>cascadePosteriorLogDensity V a L (N+1) Q z)=
      fun Q : FiniteStateField S=>V z.2+(Q+w) z.2-
        ∑i,cascadePosteriorStieltjesWeight a N i*U i Q := by
    funext Q
    rw [cascadePosteriorLogDensity_stieltjes,cascadePosteriorHistory_eq_initial_add]
  have hsum : DifferentiableAt ℝ (fun Q=>∑i,cascadePosteriorStieltjesWeight a N i*U i Q) H :=
    (ContDiff.sum fun i _=>contDiff_const.mul (hu i)).differentiable (by simp) H
  have hterm : DifferentiableAt ℝ (fun Q : FiniteStateField S=>V z.2+(Q+w) z.2) H := by
    rw [ht]
    fun_prop
  rw [hd]
  change fderiv ℝ ((fun Q : FiniteStateField S=>V z.2+(Q+w) z.2)-
    (fun Q=>∑i,cascadePosteriorStieltjesWeight a N i*U i Q)) H K = _
  rw [fderiv_sub hterm hsum,ContinuousLinearMap.sub_apply,ht,fderiv_const_add,
    ContinuousLinearMap.fderiv]
  rw [fderiv_fun_sum (fun i _=>((hu i).differentiable (by simp) H).const_mul _)]
  simp_rw [ContinuousLinearMap.sum_apply,fderiv_const_mul ((hu _).differentiable (by simp) H),
    ContinuousLinearMap.smul_apply,smul_eq_mul]
  rfl

theorem norm_cavityFinitePosteriorScore_le (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (N : ℕ)
    (H K : FiniteStateField S) (z : (Fin (N+1)→Field n)×S) :
    ‖cavityFinitePosteriorScore V a L N H K z‖ ≤ 2*‖K‖ := by
  rw [←fderiv_cascadePosteriorLogDensity_stieltjes V a ha L]
  exact ((fderiv ℝ (fun Q=>cascadePosteriorLogDensity V a L (N+1) Q z) H).le_opNorm K).trans
    (mul_le_mul_of_nonneg_right
      (by rw [←norm_iteratedFDeriv_one]; exact norm_cascadePosteriorLogDensity_firstJet_le_two V a ha ha1 hdec L _ H z)
      (norm_nonneg K))

end QuantitativeFollowup
