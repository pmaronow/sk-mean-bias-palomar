module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterStieltjes
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterNormalizer

@[expose] public section

/-! Genuine free-Stieltjes first and second scores of the full outer
posterior. The root fractional tilt changes its root charge to a(N)-s,
and the actual outer log normalizer is retained in both derivatives. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
variable {S J : Type} [Fintype S] [Nonempty S] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

private theorem smooth_outer_stieltjes_potential (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (N : ℕ)
    (z : Fin (N+1)→Field n) (B : FiniteStateField S) (i : Option (Option (Fin N))) :
    ContDiff ℝ ∞ (fun Q=>cascadePosteriorStieltjesPotential V a L N z i (Q+B)) :=by
  have hi:ContDiff ℝ ∞ (cascadePosteriorStieltjesPotential V a L N z i):=by
    cases i with
    | none=>
      dsimp only [cascadePosteriorStieltjesPotential]
      rw [cascadePosteriorHistoryPotential_eq_translate]
      exact (contDiff_finiteStateGaussianTerminalCascade V a ha L _).comp
        (contDiff_id.add contDiff_const)
    | some i=>
      cases i <;> dsimp only [cascadePosteriorStieltjesPotential] <;>
        rw [cascadePosteriorHistoryPotential_eq_translate] <;>
        exact (contDiff_finiteStateGaussianTerminalCascade V a ha L _).comp
          (contDiff_id.add contDiff_const)
  exact hi.comp (contDiff_id.add contDiff_const)

def cavityOuterPosteriorScore (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H K : FiniteStateField S)
    (p : FiniteStateGaussianInput J×((Fin (N+1)→Field n)×S)) : ℝ :=
  K p.2.2-∑i,cavityOuterStieltjesWeight a s N i*
    fderiv ℝ (fun Q=>cascadePosteriorStieltjesPotential V a L N p.2.1 i (Q+R p.1)) H K-
    fderiv ℝ (fun Q=>Real.log (cavityOuterPosteriorNormalizer V a L s (N+1) R Q)) H K

theorem fderiv_cavityOuterPosteriorLogDensity_stieltjes (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H K : FiniteStateField S)
    (p : FiniteStateGaussianInput J×((Fin (N+1)→Field n)×S)) :
    fderiv ℝ (fun Q=>cavityOuterPosteriorLogDensity V a L s (N+1) R Q p) H K=
      cavityOuterPosteriorScore V a L s N R H K p :=by
  let U:=fun i Q=>cascadePosteriorStieltjesPotential V a L N p.2.1 i (Q+R p.1)
  let w:=R p.1+cascadePosteriorHistory L (N+1) 0 p.2.1 (Fin.last (N+1))
  have hu(i):ContDiff ℝ ∞ (U i):=smooth_outer_stieltjes_potential V a ha L N p.2.1 _ i
  have hterm : (fun Q : FiniteStateField S=>V p.2.2+(Q+w) p.2.2)=
      fun Q=>V p.2.2+w p.2.2+(EuclideanSpace.proj p.2.2 : FiniteStateField S→L[ℝ]ℝ) Q :=by
    funext Q
    simp only [EuclideanSpace.coe_proj,PiLp.add_apply]
    ring
  have he : (fun Q=>cavityOuterPosteriorLogDensity V a L s (N+1) R Q p)=
      fun Q=>V p.2.2+(Q+w) p.2.2-
        ∑i,cavityOuterStieltjesWeight a s N i*U i Q-
        Real.log (cavityOuterPosteriorNormalizer V a L s (N+1) R Q) :=by
    funext Q
    rw [cavityOuterPosteriorLogDensity_stieltjes,cascadePosteriorHistory_eq_initial_add]
    simp only [U,w,add_assoc]
  have hs : DifferentiableAt ℝ (fun Q=>∑i,cavityOuterStieltjesWeight a s N i*U i Q) H:=
    (ContDiff.sum fun i _=>contDiff_const.mul (hu i)).differentiable (by simp) H
  have ht : DifferentiableAt ℝ (fun Q : FiniteStateField S=>V p.2.2+(Q+w) p.2.2) H:=by
    rw [hterm]
    fun_prop
  have hz:=(contDiff_log_cavityOuterPosteriorNormalizer V a ha L s (N+1) R).differentiable (by simp) H
  rw [he]
  change fderiv ℝ (((fun Q : FiniteStateField S=>V p.2.2+(Q+w) p.2.2)-
    (fun Q=>∑i,cavityOuterStieltjesWeight a s N i*U i Q))-
    (fun Q=>Real.log (cavityOuterPosteriorNormalizer V a L s (N+1) R Q))) H K=_
  rw [fderiv_sub (ht.sub hs) hz,ContinuousLinearMap.sub_apply,
    fderiv_sub ht hs,ContinuousLinearMap.sub_apply,hterm,fderiv_const_add,ContinuousLinearMap.fderiv,
    fderiv_fun_sum (fun i _=>((hu i).differentiable (by simp) H).const_mul _)]
  simp only [ContinuousLinearMap.sum_apply,fderiv_const_mul ((hu _).differentiable (by simp) H),
    ContinuousLinearMap.smul_apply,smul_eq_mul]
  rfl

def cavityOuterPosteriorSecondScore (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H K : FiniteStateField S)
    (p : FiniteStateGaussianInput J×((Fin (N+1)→Field n)×S)) : ℝ :=
  -(∑i,cavityOuterStieltjesWeight a s N i*
    fderiv ℝ (fun Q=>fderiv ℝ
      (fun B=>cascadePosteriorStieltjesPotential V a L N p.2.1 i (B+R p.1)) Q K) H K)-
    fderiv ℝ (fun Q=>fderiv ℝ
      (fun B=>Real.log (cavityOuterPosteriorNormalizer V a L s (N+1) R B)) Q K) H K

theorem second_fderiv_cavityOuterPosteriorLogDensity_stieltjes (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H K : FiniteStateField S)
    (p : FiniteStateGaussianInput J×((Fin (N+1)→Field n)×S)) :
    fderiv ℝ (fun Q=>fderiv ℝ
      (fun B=>cavityOuterPosteriorLogDensity V a L s (N+1) R B p) Q K) H K=
      cavityOuterPosteriorSecondScore V a L s N R H K p :=by
  let U:=fun i Q=>cascadePosteriorStieltjesPotential V a L N p.2.1 i (Q+R p.1)
  have hu(i):ContDiff ℝ ∞ (U i):=smooth_outer_stieltjes_potential V a ha L N p.2.1 _ i
  have hd(i):DifferentiableAt ℝ (fun Q=>fderiv ℝ (U i) Q K) H:=
    (((hu i).fderiv_right (m:=∞) (by simp)).differentiable (by simp) H).clm_apply
      (differentiableAt_const K)
  have hz: DifferentiableAt ℝ (fun Q=>fderiv ℝ
      (fun B=>Real.log (cavityOuterPosteriorNormalizer V a L s (N+1) R B)) Q K) H:=
    (((contDiff_log_cavityOuterPosteriorNormalizer V a ha L s (N+1) R).fderiv_right
      (m:=∞) (by simp)).differentiable (by simp) H).clm_apply (differentiableAt_const K)
  have he : (fun Q=>fderiv ℝ (fun B=>cavityOuterPosteriorLogDensity V a L s (N+1) R B p) Q K)=
      fun Q=>K p.2.2-∑i,cavityOuterStieltjesWeight a s N i*fderiv ℝ (U i) Q K-
        fderiv ℝ (fun B=>Real.log (cavityOuterPosteriorNormalizer V a L s (N+1) R B)) Q K:=
    funext fun Q=>fderiv_cavityOuterPosteriorLogDensity_stieltjes V a ha L s N R Q K p
  rw [he]
  have hs: DifferentiableAt ℝ (fun Q=>∑i,cavityOuterStieltjesWeight a s N i*fderiv ℝ (U i) Q K) H:=
    DifferentiableAt.fun_sum (fun i _=>(hd i).const_mul _)
  change fderiv ℝ (((fun _ : FiniteStateField S=>K p.2.2)-
    (fun Q=>∑i,cavityOuterStieltjesWeight a s N i*fderiv ℝ (U i) Q K))-
    (fun Q=>fderiv ℝ (fun B=>Real.log (cavityOuterPosteriorNormalizer V a L s (N+1) R B)) Q K)) H K=_
  rw [fderiv_sub ((differentiableAt_const (K p.2.2)).sub hs) hz,
    ContinuousLinearMap.sub_apply,fderiv_sub (differentiableAt_const (K p.2.2)) hs,fderiv_const_apply,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.zero_apply,zero_sub,
    fderiv_fun_sum (fun i _=>(hd i).const_mul _)]
  simp only [ContinuousLinearMap.sum_apply,fderiv_const_mul (hd _),
    ContinuousLinearMap.smul_apply,smul_eq_mul]
  rfl

end QuantitativeFollowup
