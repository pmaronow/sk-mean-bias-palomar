module
public import QuantitativePaper.VectorProfileGradientScoreMoment

@[expose] public section

/-! Literal second affine-profile score of the genuine posterior density.
The positive Stieltjes weights retain total mass one. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem hasDerivAt_vectorProfilePosteriorLogDensity_deriv (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (p : Couplings n×ℝ) (x : Field n) (N : ℕ) (θ : ℝ)
    (z : (Fin (N+1)→Field n)×Configuration n) :
    HasDerivAt (deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z))
      (-(∑i : Option (Fin N), (
        2*vectorProfilePosteriorDirection s₀ s₁ N i*
          deriv (fun φ=>vectorProfilePosteriorPotential s₀ s₁ β t p x N z.1 φ i) θ+
        vectorProfilePosteriorWeight s₀ s₁ N θ i*
          deriv (deriv (fun φ=>vectorProfilePosteriorPotential s₀ s₁ β t p x N z.1 φ i)) θ))) θ := by
  let P:=fun (i : Option (Fin N)) (φ : ℝ)=>vectorProfilePosteriorPotential s₀ s₁ β t p x N z.1 φ i
  let D:=vectorProfilePosteriorDirection s₀ s₁ N
  let a:=vectorProfilePosteriorWeight s₀ s₁ N
  have hP (i : Option (Fin N)) : ContDiff ℝ ∞ (P i):=
    contDiff_vectorProfilePosteriorPotential_theta s₀ s₁ β t p x N z.1 i
  have hPD (i : Option (Fin N)) : HasDerivAt (P i) (deriv (P i) θ) θ:=
    ((hP i).differentiable (by simp) θ).hasDerivAt
  have hPDD (i : Option (Fin N)) : HasDerivAt (deriv (P i)) (deriv (deriv (P i)) θ) θ:=
    (((hP i).of_le (by norm_num : (2:ℕ∞ω)≤∞)).differentiable_deriv_two θ).hasDerivAt
  have hd:=HasDerivAt.sum (u:=Finset.univ) (fun (i : Option (Fin N)) _=>
    ((hPD i).const_mul (D i)).add
      ((hasDerivAt_vectorProfilePosteriorWeight s₀ s₁ N i θ).mul (hPDD i))) |>.neg
  have he : deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z)=
      (fun φ=>-(∑i : Option (Fin N),(D i*P i φ+a φ i*deriv (P i) φ))) := by
    funext φ
    exact (hasDerivAt_vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z).deriv
  rw [he]
  convert hd using 1
  · funext φ
    simp only [Pi.neg_apply,Finset.sum_apply,Pi.add_apply,Pi.mul_apply]
    rfl
  · apply congrArg Neg.neg
    apply Finset.sum_congr rfl
    intro i _
    change 2*D i*deriv (P i) θ+a θ i*deriv (deriv (P i)) θ=
      D i*deriv (P i) θ+(D i*deriv (P i) θ+a θ i*deriv (deriv (P i)) θ)
    ring

theorem vectorProfilePosteriorLogDensity_second_deriv_bound_of_potential_bound
    (s₀ s₁ : RSBScheme k) (hgrid : ∀i,i≤k+2→s₀.q i=s₁.q i)
    (β t θ : ℝ) (ht : t≤1) (hθ : θ∈Ioo (0:ℝ) 1)
    (p : Couplings n×ℝ) (x : Field n) (N : ℕ) (hN : N+1≤k+2)
    (z : (Fin (N+1)→Field n)×Configuration n) (Q : ℝ) (hQ : 0≤Q)
    (hsecond : ∀i : Option (Fin N),
      |deriv (deriv (fun φ=>vectorProfilePosteriorPotential s₀ s₁ β t p x N z.1 φ i)) θ|≤Q) :
    |deriv (deriv (fun φ=>vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z)) θ|≤
      4*((n:ℝ)*((1-t)*β^2)/2)+Q := by
  let B:=(n:ℝ)*((1-t)*β^2)/2
  have hB : 0≤B:=by dsimp only [B];positivity
  rw [(hasDerivAt_vectorProfilePosteriorLogDensity_deriv s₀ s₁ β t p x N θ z).deriv,abs_neg]
  calc
    _ ≤ ∑i : Option (Fin N),
        |2*vectorProfilePosteriorDirection s₀ s₁ N i*
          deriv (fun φ=>vectorProfilePosteriorPotential s₀ s₁ β t p x N z.1 φ i) θ+
        vectorProfilePosteriorWeight s₀ s₁ N θ i*
          deriv (deriv (fun φ=>vectorProfilePosteriorPotential s₀ s₁ β t p x N z.1 φ i)) θ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑i : Option (Fin N), (
        2*|vectorProfilePosteriorDirection s₀ s₁ N i| * B+
          vectorProfilePosteriorWeight s₀ s₁ N θ i*Q) := by
      apply Finset.sum_le_sum
      intro i _
      apply (abs_add_le _ _).trans
      apply add_le_add
      · rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
        exact mul_le_mul_of_nonneg_left
          (by simpa only [Real.norm_eq_abs] using
            (norm_vectorProfilePosteriorPotential_deriv_le s₀ s₁ hgrid β t θ ht hθ p x N hN z.1 i))
          (by positivity)
      · rw [abs_mul,abs_of_nonneg (vectorProfilePosteriorWeight_nonneg s₀ s₁ N hN θ ⟨hθ.1.le,hθ.2.le⟩ i)]
        exact mul_le_mul_of_nonneg_left (hsecond i)
          (vectorProfilePosteriorWeight_nonneg s₀ s₁ N hN θ ⟨hθ.1.le,hθ.2.le⟩ i)
    _ = 2*(∑i : Option (Fin N),|vectorProfilePosteriorDirection s₀ s₁ N i|)*B+Q := by
      rw [Finset.sum_add_distrib,←Finset.sum_mul,←Finset.sum_mul,←Finset.mul_sum,
        vectorProfilePosteriorWeight_sum s₀ s₁ N hN θ,one_mul]
    _ ≤ 4*B+Q := by
      have hh:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (vectorProfilePosteriorDirection_total_variation_le s₀ s₁ N hN)
          (by norm_num : (0:ℝ)≤2)) hB
      nlinarith

end QuantitativePaper
