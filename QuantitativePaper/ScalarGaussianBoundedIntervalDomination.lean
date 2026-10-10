module
public import QuantitativePaper.ScalarParameterSliceJets
public import QuantitativePaper.ScalarDominatedIntegral

@[expose] public section

/-! Gaussian domination with the actual retained-coordinate linear inclusion. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace QuantitativePaper
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
set_option maxHeartbeats 1400000

theorem scalarGaussianLinearDominatedJets_on_bounded_interval (N : ℕ) (μ : Measure E)
    (hμ : ∀D : ℝ,Integrable (fun p : E=>Real.exp (D*‖p‖)) μ)
    (L : E→L[ℝ]F) (f : ℝ×F→ℝ) (a b : ℝ)
    (hf : ∀z : ℝ×F,z.1∈Ioo a b → ContDiffAt ℝ ∞ f z)
    (C D : ℝ) (hC : 0≤C) (hD : 0≤D)
    (hj : ∀r,r≤N→∀z : ℝ×F,z.1∈Ioo a b→
      ‖iteratedFDeriv ℝ r f z‖≤C*Real.exp (D*‖z‖)) :
    ScalarDominatedJets N μ (fun θ p=>f (θ,L p)) (Ioo a b) := by
  refine ⟨?_,?_,?_⟩
  · intro p θ hθ
    have hs : ContDiffAt ℝ ∞ (fun θ=>f (θ,L p)) θ:=
      (hf (θ,L p) hθ).comp θ (contDiffAt_id.prodMk contDiffAt_const)
    exact (hs.of_le (by simp)).contDiffWithinAt
  · intro r hr θ hθ
    exact ((continuous_iteratedFDeriv_scalarParameterSlice f a b hf θ hθ r).comp L.continuous).aestronglyMeasurable
  · intro θ hθ
    let M:=max |a| |b|
    let B:=fun _ : ℕ=>fun p : E=>C*Real.exp (D*M)*Real.exp ((D*‖L‖)*‖p‖)
    refine ⟨Ioo a b,isOpen_Ioo.mem_nhds hθ,subset_rfl,B,
      fun _ _=>(hμ (D*‖L‖)).const_mul _,?_⟩
    intro r hr y hy p
    have hM : 0≤M:=(abs_nonneg a).trans (le_max_left _ _)
    have hyM : |y|≤M:=by
      rw [abs_le]
      constructor
      · have hh:=neg_abs_le a
        have hma : |a|≤M:=le_max_left _ _
        linarith [hy.1]
      · have hh:=le_abs_self b
        have hmb : |b|≤M:=le_max_right _ _
        linarith [hy.2]
    have hnorm : ‖(y,L p)‖≤M+‖L‖*‖p‖:=by
      change max ‖y‖ ‖L p‖≤_
      rw [Real.norm_eq_abs]
      exact max_le (by linarith [mul_nonneg (norm_nonneg L) (norm_nonneg p)])
        ((L.le_opNorm p).trans (by linarith))
    apply (norm_iteratedFDeriv_scalarParameterSlice_le f a b hf y hy (L p) r).trans
    apply (hj r hr (y,L p) hy).trans
    dsimp only [B]
    calc
      C*Real.exp (D*‖(y,L p)‖)≤C*Real.exp (D*(M+‖L‖*‖p‖)):=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left hnorm hD)) hC
      _=C*Real.exp (D*M)*Real.exp ((D*‖L‖)*‖p‖):=by
        rw [show D*(M+‖L‖*‖p‖)=D*M+(D*‖L‖)*‖p‖ by ring,Real.exp_add]
        ring

end QuantitativePaper
