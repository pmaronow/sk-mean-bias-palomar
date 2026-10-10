module
public import FourPapersCommon.DerivativeInterpolation

@[expose] public section

/-! A uniform limit has the genuine derivative obtained from uniform
derivative approximation, when the approximating derivatives share a Lipschitz
bound. Cauchy estimates and existence of the derivative limit are discharged. -/
noncomputable section
open Set Filter
open scoped NNReal Topology
namespace FourPapersCommon
set_option maxHeartbeats 800000
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem uniformCauchySeqOn_fderiv_of_uniformCauchy (f : ℕ→E→F)
    (hf : ∀j,Differentiable ℝ (f j)) (L : ℝ≥0)
    (hL : ∀j,LipschitzWith L (fderiv ℝ (f j)))
    (hu : UniformCauchySeqOn f atTop univ) :
    UniformCauchySeqOn (fun j => fderiv ℝ (f j)) atTop univ := by
  rw [Metric.uniformCauchySeqOn_iff] at hu ⊢
  intro ε hε
  let δ : ℝ := ε/(8*(L+1))
  have hδ : 0<δ := by dsimp only [δ];positivity
  obtain ⟨N,hN⟩ := hu (ε*δ/8) (by positivity)
  refine ⟨N,fun j hj k hk x _ => ?_⟩
  have hb (y : E) : ‖f j y-f k y‖ ≤ ε*δ/8 := by
    have hh := hN j hj k hk y (mem_univ _)
    simpa only [dist_eq_norm] using hh.le
  rw [dist_eq_norm]
  apply (norm_fderiv_sub_le_of_uniform_sub_Banach (f j) (f k) (hf j) (hf k)
    L (hL j) (hL k) (ε*δ/8) (by positivity) hb δ hδ x).trans_lt
  have hL0 : 0 ≤ (L : ℝ) := L.coe_nonneg
  have hL1 : 0<(L : ℝ)+1 := by positivity
  have he : 2*(ε*δ/8)/δ=ε/4 := by field_simp;ring
  rw [he]
  have hbδ : 2*(L : ℝ)*δ ≤ ε/4 := by
    dsimp only [δ]
    have he : 2*(L : ℝ)*(ε/(8*(L+1)))=(L*ε/4)/(L+1) := by field_simp;ring
    rw [he]
    exact (div_le_iff₀ hL1).mpr (by nlinarith)
  linarith

theorem exists_uniform_derivative_limit (f : ℕ→E→F) (g : E→F)
    (hf : ∀j,ContDiff ℝ 2 (f j)) (L : ℝ≥0)
    (hL : ∀j,LipschitzWith L (fderiv ℝ (f j))) (hu : TendstoUniformly f g atTop) :
    ∃ g' : E→(E→L[ℝ]F),TendstoUniformly (fun j => fderiv ℝ (f j)) g' atTop ∧
      (∀x,HasFDerivAt g (g' x) x) ∧ Continuous g' := by
  have hc := uniformCauchySeqOn_fderiv_of_uniformCauchy f
    (fun j => (hf j).differentiable (by norm_num)) L hL
    (tendstoUniformlyOn_univ.mpr hu).uniformCauchySeqOn
  let g' := fun x => limUnder atTop (fun j => fderiv ℝ (f j) x)
  have ht (x : E) : Tendsto (fun j => fderiv ℝ (f j) x) atTop (𝓝 (g' x)) :=
    (hc.cauchySeq (mem_univ x)).tendsto_limUnder
  have hU := tendstoUniformlyOn_univ.mp (hc.tendstoUniformlyOn_of_tendsto (fun x _ => ht x))
  refine ⟨g',hU,fun x => hasFDerivAt_of_tendstoUniformly hU
    (fun j x => ((hf j).differentiable (by norm_num) x).hasFDerivAt)
    (fun x => hu.tendsto_at x) x,?_⟩
  exact hU.continuous (Eventually.of_forall (fun j =>
    (hf j).continuous_fderiv (by norm_num)) |>.frequently)

end FourPapersCommon
