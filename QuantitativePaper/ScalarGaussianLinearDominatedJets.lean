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

theorem scalarGaussianLinearDominatedJets (N : ℕ) (μ : Measure E)
    (hμ : ∀D : ℝ,Integrable (fun p : E=>Real.exp (D*‖p‖)) μ)
    (L : E→L[ℝ]F) (f : ℝ×F→ℝ) (a b : ℝ) (ha : 0<a) (hb : b<1)
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
    let B:=fun _ : ℕ=>fun p : E=>C*Real.exp D*Real.exp ((D*‖L‖)*‖p‖)
    refine ⟨Ioo a b,isOpen_Ioo.mem_nhds hθ,subset_rfl,B,
      fun _ _=>(hμ (D*‖L‖)).const_mul _,?_⟩
    intro r hr y hy p
    have hnorm : ‖(y,L p)‖≤1+‖L‖*‖p‖:=by
      have hy0 : 0≤y:=(ha.trans hy.1).le
      have hy1 : y≤1:=(hy.2.trans hb).le
      change max ‖y‖ ‖L p‖≤_
      rw [Real.norm_eq_abs,abs_of_nonneg hy0]
      exact max_le (by linarith [mul_nonneg (norm_nonneg L) (norm_nonneg p)])
        ((L.le_opNorm p).trans (by linarith))
    apply (norm_iteratedFDeriv_scalarParameterSlice_le f a b hf y hy (L p) r).trans
    apply (hj r hr (y,L p) hy).trans
    dsimp only [B]
    calc
      C*Real.exp (D*‖(y,L p)‖)≤C*Real.exp (D*(1+‖L‖*‖p‖)):=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left hnorm hD)) hC
      _=C*Real.exp D*Real.exp ((D*‖L‖)*‖p‖):=by
        rw [show D*(1+‖L‖*‖p‖)=D+(D*‖L‖)*‖p‖ by ring,Real.exp_add]
        ring

end QuantitativePaper
