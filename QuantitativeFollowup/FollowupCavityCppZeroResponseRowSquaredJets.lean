module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFeatureJets

@[expose] public section

/-! Actual first and second row derivatives of the retained isolated and
rest spin squares. The second row response is a derivative of the true
finite potential, and is differentiated along each spin feature. -/
noncomputable section
open Set FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
variable {S : Type} [Fintype S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityFiniteEnergyRowSecond (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ) (K H : FiniteStateField S) : ℝ :=
  fderiv ℝ (fun Q=>fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) Q K) H K

theorem cavityFiniteEnergyFeatureSquare_second_row (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ)
    (H b K : FiniteStateField S) :
    fderiv ℝ (fun Q=>fderiv ℝ
      (fun R=>(cavityFiniteEnergyFeatureMean V a L j b R)^2) Q K) H K=
      2*(fderiv ℝ (cavityFiniteEnergyFeatureMean V a L j b) H K)^2+
      2*cavityFiniteEnergyFeatureMean V a L j b H*
        fderiv ℝ (cavityFiniteEnergyRowSecond V a L j K) H b :=by
  rw [cavityFiniteEnergyFeatureSquare_second V a ha L j H b K,
    cavityFiniteEnergyFeatureMean_second_exchange V a ha L j H b K]
  rfl

variable {ι : Type} [Fintype ι]

theorem cavityFiniteEnergyRestOverlap_first_row (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ)
    (b : ι→FiniteStateField S) (H K : FiniteStateField S) :
    fderiv ℝ (cavityFiniteEnergyRestOverlap V a L j b) H K=
      2*(Fintype.card ι : ℝ)⁻¹*∑i,cavityFiniteEnergyFeatureMean V a L j (b i) H*
        fderiv ℝ (cavityFiniteEnergyFeatureMean V a L j (b i)) H K :=by
  have hd (i : ι):DifferentiableAt ℝ
      (fun Q=>(cavityFiniteEnergyFeatureMean V a L j (b i) Q)^2) H:=
    ((boundedJets_cavityFiniteEnergyFeatureMean V a ha L j (b i)).1.differentiable (by simp) H).pow 2
  unfold cavityFiniteEnergyRestOverlap
  rw [fderiv_const_mul (DifferentiableAt.fun_sum (fun i _=>hd i)),
    ContinuousLinearMap.smul_apply,smul_eq_mul,fderiv_fun_sum (fun i _=>hd i),
    ContinuousLinearMap.sum_apply]
  simp_rw [cavityFiniteEnergyFeatureSquare_first V a ha L j]
  simp_rw [mul_assoc]
  rw [←Finset.mul_sum]
  ring

theorem cavityFiniteEnergyRestOverlap_second_row (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (j : ℕ)
    (b : ι→FiniteStateField S) (H K : FiniteStateField S) :
    fderiv ℝ (fun Q=>fderiv ℝ (cavityFiniteEnergyRestOverlap V a L j b) Q K) H K=
      2*(Fintype.card ι : ℝ)⁻¹*∑i,
        ((fderiv ℝ (cavityFiniteEnergyFeatureMean V a L j (b i)) H K)^2+
        cavityFiniteEnergyFeatureMean V a L j (b i) H*
          fderiv ℝ (cavityFiniteEnergyRowSecond V a L j K) H (b i)) :=by
  let F:=fun i : ι=>cavityFiniteEnergyFeatureMean V a L j (b i)
  have hd (i : ι):ContDiff ℝ ∞ (fun Q=>fderiv ℝ (fun R=>(F i R)^2) Q K):=
    (((boundedJets_cavityFiniteEnergyFeatureMean V a ha L j (b i)).1.pow 2).fderiv_right
      (by simp)).clm_apply (contDiff_const (c:=K))
  have hfirst : (fun Q=>fderiv ℝ (cavityFiniteEnergyRestOverlap V a L j b) Q K)=
      fun Q=>(Fintype.card ι : ℝ)⁻¹*∑i,fderiv ℝ (fun R=>(F i R)^2) Q K :=by
    funext Q
    rw [cavityFiniteEnergyRestOverlap_first_row V a ha L j b]
    simp_rw [F,cavityFiniteEnergyFeatureSquare_first V a ha L j]
    simp_rw [mul_assoc]
    rw [←Finset.mul_sum]
    ring
  rw [hfirst,fderiv_const_mul (DifferentiableAt.fun_sum
    (fun i _=>(hd i).differentiable (by simp) H)),ContinuousLinearMap.smul_apply,smul_eq_mul,
    fderiv_fun_sum (fun i _=>(hd i).differentiable (by simp) H),ContinuousLinearMap.sum_apply]
  simp only [F]
  simp_rw [cavityFiniteEnergyFeatureSquare_second_row V a ha L j]
  simp_rw [mul_assoc,←mul_add]
  rw [←Finset.mul_sum]
  ring

end QuantitativeFollowup
