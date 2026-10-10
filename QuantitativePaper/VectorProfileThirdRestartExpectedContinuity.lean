module
public import QuantitativePaper.VectorProfileThirdDerivativeEnvelopes
public import FourPapersCommon.RetainedExponentialContinuous
public import QuantitativePaper.VectorRestartExpectedContinuity

@[expose] public section

/-! Closed-cell continuity of actual restarted expected third profile
variations, obtained from retained Gaussian jets and the true path envelope. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem continuousOn_vectorProfile_third_restart_expectation
    (μ : Paper.ParisiMeasure) (s₀ s₁ : RSBScheme k) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) (i : ℕ) (hi : i≤k+1)
    (a b : ℝ) (ha : 0≤a) (hb : b≤1)
    (hcell : ∀r∈Icc a b,(q:ℝ)+r∈Icc (s₀.q i) (s₀.q (i+1))) :
    ContinuousOn (fun r=>∫sample : VectorDisorderBrownianSample n,
      vectorProfileCellPotentialThirdVariation s₀ s₁ β t i ((q:ℝ)+r,θ,p)
        (vectorRestartState μ β t ht q p x r.toNNReal sample)
      ∂vectorDisorderBrownianMeasure n) (Icc a b) := by
  let A:=θ/2
  let B:=(θ+1)/2
  have hA : 0<A:=by dsimp [A];linarith [hθ.1]
  have hB : B<1:=by dsimp [B];linarith [hθ.2]
  have hθAB : θ∈Ioo A B:=⟨by dsimp [A];linarith [hθ.1],by dsimp [B];linarith [hθ.2]⟩
  have hF:=(retainedJetExponentialOn_vectorProfileCellPotentialThirdVariation
    (n:=n) s₀ s₁ β t ht i hi A B hA hB).values
  let F : ℝ×Field n→ℝ:=fun z=>
    vectorProfileCellPotentialThirdVariation s₀ s₁ β t i ((q:ℝ)+z.1,θ,p) z.2
  have hFC : ContinuousOn F (Icc a b×ˢuniv):=by
    exact hF.continuous.comp
      (f:=fun z : ℝ×Field n=>((q:ℝ)+z.1,((θ,p),z.2)))
      (g:=fun z : ℝ×(VectorProfileParameter n×Field n)=>
        vectorProfileCellPotentialThirdVariation s₀ s₁ β t i (z.1,z.2.1) z.2.2)
      (show Continuous (fun z : ℝ×Field n=>((q:ℝ)+z.1,((θ,p),z.2))) by fun_prop).continuousOn
      (fun z hz=>⟨hcell z.1 hz.1,hθAB⟩)
  obtain ⟨C,R,hC,hR,hbound⟩:=hF.bound
  apply continuousOn_vectorRestart_expected_exp_test μ β t ht q p x a b ha hb F hFC
    (C*Real.exp (R*(|θ|+‖p‖))) R (by positivity) hR
  intro r hr y
  have hn : ‖(((θ,p),y) : VectorProfileParameter n×Field n)‖≤|θ|+‖p‖+‖y‖:=by
    change max (max |θ| ‖p‖) ‖y‖≤_
    apply max_le
    · apply max_le <;> linarith [abs_nonneg θ,norm_nonneg p,norm_nonneg y]
    · linarith [abs_nonneg θ,norm_nonneg p]
  have hh:=hbound ((q:ℝ)+r) (hcell r hr) ((θ,p),y) hθAB
  change |vectorProfileCellPotentialThirdVariation s₀ s₁ β t i ((q:ℝ)+r,θ,p) y|≤_
  rw [←Real.norm_eq_abs]
  exact hh.trans ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left hn hR)) hC).trans_eq (by
      rw [show R*(|θ|+‖p‖+‖y‖)=R*(|θ|+‖p‖)+R*‖y‖ by ring,Real.exp_add];ring))

end QuantitativePaper
