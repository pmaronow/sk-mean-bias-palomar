module
public import FourPapersCommon.UniformDerivativeLimit

@[expose] public section

/-! Uniform derivative convergence over every parameter, from true uniform
value convergence, uniform spatial Lipschitz derivatives, and the separately
identified pointwise derivative limit. -/
noncomputable section
open Set Filter
open scoped NNReal Topology
namespace FourPapersCommon
set_option maxHeartbeats 800000
variable {A E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem uniformCauchySeqOn_fderiv_family (f : ℕ→A→E→F)
    (hf : ∀j a,Differentiable ℝ (f j a)) (L : ℝ≥0)
    (hL : ∀j a,LipschitzWith L (fderiv ℝ (f j a)))
    (hu : UniformCauchySeqOn (fun j (z : A×E) => f j z.1 z.2) atTop univ) :
    UniformCauchySeqOn (fun j (z : A×E) => fderiv ℝ (f j z.1) z.2) atTop univ := by
  rw [Metric.uniformCauchySeqOn_iff] at hu ⊢
  intro ε hε
  let δ : ℝ := ε/(8*(L+1))
  have hδ : 0<δ := by dsimp only [δ];positivity
  obtain ⟨N,hN⟩ := hu (ε*δ/8) (by positivity)
  refine ⟨N,fun j hj k hk z _ => ?_⟩
  have hb (y : E) : ‖f j z.1 y-f k z.1 y‖ ≤ ε*δ/8 := by
    have hh := hN j hj k hk (z.1,y) (mem_univ _)
    simpa only [dist_eq_norm] using hh.le
  rw [dist_eq_norm]
  apply (norm_fderiv_sub_le_of_uniform_sub_Banach (f j z.1) (f k z.1)
    (hf j z.1) (hf k z.1) L (hL j z.1) (hL k z.1)
    (ε*δ/8) (by positivity) hb δ hδ z.2).trans_lt
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

theorem tendstoUniformly_fderiv_family (f : ℕ→A→E→F) (D : A×E→E→L[ℝ]F)
    (hf : ∀j a,Differentiable ℝ (f j a)) (L : ℝ≥0)
    (hL : ∀j a,LipschitzWith L (fderiv ℝ (f j a)))
    (hu : UniformCauchySeqOn (fun j (z : A×E) => f j z.1 z.2) atTop univ)
    (ht : ∀z,Tendsto (fun j => fderiv ℝ (f j z.1) z.2) atTop (𝓝 (D z))) :
    TendstoUniformly (fun j (z : A×E) => fderiv ℝ (f j z.1) z.2) D atTop := by
  exact tendstoUniformlyOn_univ.mp
    ((uniformCauchySeqOn_fderiv_family f hf L hL hu).tendstoUniformlyOn_of_tendsto (fun z _ => ht z))

end FourPapersCommon
