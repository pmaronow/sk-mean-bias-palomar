module
public import QuantitativePaper.VectorProfileRestartExpectedContinuity
public import QuantitativePaper.VectorRestartTestIntegrability

@[expose] public section

/-! Every closed-cell second profile variation is integrable under the
actual restarted state law, without an endpoint integrability premise. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem integrable_vectorProfile_second_restart_test
    (μ : Paper.ParisiMeasure) (s₀ s₁ : RSBScheme k) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) (i : ℕ) (hi : i≤k+1)
    (r : ℝ≥0) (hr1 : r≤1) (hr : (q:ℝ)+(r:ℝ)∈Icc (s₀.q i) (s₀.q (i+1))) :
    Integrable (fun sample : VectorDisorderBrownianSample n=>
      vectorProfileCellPotentialSecondVariation s₀ s₁ β t i ((q:ℝ)+r,θ,p)
        (vectorRestartState μ β t ht q p x r sample)) (vectorDisorderBrownianMeasure n) := by
  let A:=θ/2
  let B:=(θ+1)/2
  have hA : 0<A:=by dsimp [A];linarith [hθ.1]
  have hB : B<1:=by dsimp [B];linarith [hθ.2]
  have hθAB : θ∈Ioo A B:=⟨by dsimp [A];linarith [hθ.1],by dsimp [B];linarith [hθ.2]⟩
  have hF:=(retainedJetExponentialOn_vectorProfileCellPotentialSecondVariation
    (n:=n) s₀ s₁ β t ht i hi A B hA hB).values
  have hFC : Continuous (vectorProfileCellPotentialSecondVariation s₀ s₁ β t i ((q:ℝ)+r,θ,p)):=by
    rw [←continuousOn_univ]
    exact hF.continuous.comp
      (f:=fun y : Field n=>((q:ℝ)+r,((θ,p),y)))
      (g:=fun z : ℝ×(VectorProfileParameter n×Field n)=>
        vectorProfileCellPotentialSecondVariation s₀ s₁ β t i (z.1,z.2.1) z.2.2)
      (show Continuous (fun y : Field n=>((q:ℝ)+r,((θ,p),y))) by fun_prop).continuousOn
      (fun _ _=>⟨hr,hθAB⟩)
  obtain ⟨C,R,hC,hR,hbound⟩:=hF.bound
  apply integrable_vectorRestart_exp_test μ β t ht q p x r hr1 _ hFC
    (C*Real.exp (R*(|θ|+‖p‖))) R (by positivity) hR
  intro y
  have hn : ‖(((θ,p),y) : VectorProfileParameter n×Field n)‖≤|θ|+‖p‖+‖y‖:=by
    change max (max |θ| ‖p‖) ‖y‖≤_
    apply max_le
    · apply max_le <;> linarith [abs_nonneg θ,norm_nonneg p,norm_nonneg y]
    · linarith [abs_nonneg θ,norm_nonneg p]
  have hh:=hbound ((q:ℝ)+r) hr ((θ,p),y) hθAB
  rw [←Real.norm_eq_abs]
  exact hh.trans ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left hn hR)) hC).trans_eq (by
      rw [show R*(|θ|+‖p‖+‖y‖)=R*(|θ|+‖p‖)+R*‖y‖ by ring,Real.exp_add];ring))

end QuantitativePaper
