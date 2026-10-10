module
public import FourPapersCommon.UniformDerivativeLimit

@[expose] public section

/-! Genuine derivative closure needs differentiability and a common Lipschitz
modulus of the actual derivatives; higher smoothness is unnecessary. -/
noncomputable section
open Set Filter FourPapersCommon
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
set_option maxHeartbeats 800000

theorem exists_uniform_derivative_limit_of_differentiable (f : ℕ→E→F) (g : E→F)
    (hf : ∀j,Differentiable ℝ (f j)) (L : ℝ≥0)
    (hL : ∀j,LipschitzWith L (fderiv ℝ (f j))) (hu : TendstoUniformly f g atTop) :
    ∃ g' : E→(E→L[ℝ]F),TendstoUniformly (fun j => fderiv ℝ (f j)) g' atTop ∧
      (∀x,HasFDerivAt g (g' x) x) ∧ Continuous g' := by
  have hc := uniformCauchySeqOn_fderiv_of_uniformCauchy f
    hf L hL
    (tendstoUniformlyOn_univ.mpr hu).uniformCauchySeqOn
  let g' := fun x => limUnder atTop (fun j => fderiv ℝ (f j) x)
  have ht (x : E) : Tendsto (fun j => fderiv ℝ (f j) x) atTop (𝓝 (g' x)) :=
    (hc.cauchySeq (mem_univ x)).tendsto_limUnder
  have hU := tendstoUniformlyOn_univ.mp (hc.tendstoUniformlyOn_of_tendsto (fun x _ => ht x))
  refine ⟨g',hU,fun x => hasFDerivAt_of_tendstoUniformly hU
    (fun j x => (hf j x).hasFDerivAt)
    (fun x => hu.tendsto_at x) x,?_⟩
  exact hU.continuous (Eventually.of_forall (fun j =>
    (hL j).continuous) |>.frequently)

end QuantitativeFollowup
