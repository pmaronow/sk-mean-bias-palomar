module
public import HexagonPaper.PathHeatClockKernelFamily
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section

/-! The manuscript's continuous clock derivative on its compact parameter
interval gives the uniform raw covariance-kernel bound used by the actual
Fernique/Price assembly; it is derived, not a further source hypothesis. -/
noncomputable section
open Set Filter
open scoped Topology unitInterval NNReal
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem exists_pathHeatClockRawKernel_bound_of_continuous
    {Z : Type*} [TopologicalSpace Z] [CompactSpace Z] {L : ℕ}
    (dc : Z→Fin L→C(I,ℝ)) (hdc : ∀l,Continuous (fun z=>dc z l)) :
    ∃κ : ℝ≥0,∀z,‖pathHeatClockRawKernel (dc z)‖≤κ := by
  have hprofile := continuous_pathHeatClockProfile_family dc hdc
  have hF : Continuous (fun p : Z×(Fin L×I)=>dc p.1 p.2.1 p.2.2) := by
    exact continuous_eval.comp ((hprofile.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨R,hR⟩ := isCompact_univ.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨Real.toNNReal R,fun z=>?_⟩
  apply (norm_pathHeatClockRawKernel_le (dc z)).trans
  apply (ContinuousMap.norm_le _ (Real.toNNReal R).coe_nonneg).mpr
  intro x
  exact (hR (z,x) (mem_univ _)).trans (Real.le_coe_toNNReal R)

end HexagonPaper
