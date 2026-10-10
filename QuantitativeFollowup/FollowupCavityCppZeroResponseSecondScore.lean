module
public import QuantitativeFollowup.FollowupCavitySignedResponseFiniteScore

@[expose] public section

/-! The second log-density response is the genuine Stieltjes sum of the
finite cascade's second responses. Terminal affine energy contributes zero. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
variable {S : Type} [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

def cavityFinitePosteriorSecondScore (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (N : ℕ)
    (H K : FiniteStateField S) (z : (Fin (N+1)→Field n)×S) : ℝ :=
  -(∑i,cascadePosteriorStieltjesWeight a N i*
    fderiv ℝ (fun Q=>fderiv ℝ (cascadePosteriorStieltjesPotential V a L N z.1 i) Q K) H K)

theorem fderiv_cascadePosterior_directional_score_stieltjes (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (N : ℕ)
    (H K : FiniteStateField S) (z : (Fin (N+1)→Field n)×S) :
    fderiv ℝ (fun Q=>fderiv ℝ (fun R=>cascadePosteriorLogDensity V a L (N+1) R z) Q K) H K=
      cavityFinitePosteriorSecondScore V a L N H K z := by
  let U:=cascadePosteriorStieltjesPotential V a L N z.1
  have hu (i : Option (Option (Fin N))) : ContDiff ℝ ∞ (U i) :=by
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
  have hd (i : Option (Option (Fin N))) : DifferentiableAt ℝ
      (fun Q=>fderiv ℝ (U i) Q K) H :=
    (((hu i).fderiv_right (m:=∞) (by simp)).differentiable (by simp) H).clm_apply
      (differentiableAt_const K)
  have he : (fun Q=>fderiv ℝ (fun R=>cascadePosteriorLogDensity V a L (N+1) R z) Q K)=
      fun Q=>K z.2-∑i,cascadePosteriorStieltjesWeight a N i*fderiv ℝ (U i) Q K :=by
    funext Q
    exact fderiv_cascadePosteriorLogDensity_stieltjes V a ha L N Q K z
  rw [he,fderiv_const_sub (K z.2),
    ContinuousLinearMap.neg_apply,fderiv_fun_sum (fun i _=>(hd i).const_mul _)]
  simp only [ContinuousLinearMap.sum_apply,fderiv_const_mul (hd _),
    ContinuousLinearMap.smul_apply,smul_eq_mul]
  rfl

end QuantitativeFollowup
