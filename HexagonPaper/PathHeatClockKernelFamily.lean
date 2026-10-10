module
public import HexagonPaper.PathHeatClockKernel

@[expose] public section

/-! Joint continuity and explicit bounds for the actual continuous Wiener
clock kernel. The compact-open family topology is handled by joint evaluation.
-/
noncomputable section
open Set Filter
open scoped unitInterval Topology BigOperators
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem continuous_pathHeatClockProfile_family {Z : Type*} [TopologicalSpace Z]
    {L : ℕ} (c : Z → Fin L → C(I,ℝ)) (hc : ∀l, Continuous (fun z => c z l)) :
    Continuous (fun z => pathHeatClockProfile (c z)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have h : Continuous (fun x : Fin L × (Z × I) => c x.2.1 x.1 x.2.2) := by
    apply continuous_prod_of_discrete_left.mpr
    intro l
    exact continuous_eval.comp (((hc l).comp continuous_fst).prodMk continuous_snd)
  have hp : Continuous (fun x : Z × (Fin L × I) => (x.2.1,(x.1,x.2.2))) :=
    continuous_snd.fst.prodMk (continuous_fst.prodMk continuous_snd.snd)
  exact h.comp hp

theorem continuous_pathHeatRawClockKernel_family {Z : Type*} [TopologicalSpace Z]
    {L : ℕ} (c : Z → Fin L → C(I,ℝ)) (hc : ∀l, Continuous (fun z => c z l)) :
    Continuous (fun z => pathHeatClockRawKernel (c z)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  apply ContinuousMap.continuous_of_continuous_uncurry
  let D : ((Z × (Fin L × I)) × (Fin L × I)) → ℝ :=
    fun x => if x.1.2.1=x.2.1 then 1 else 0
  have hD : Continuous D :=
    pathHeatClockEdgeIndicator.continuous.comp
      (continuous_fst.snd.fst.prodMk continuous_snd.fst)
  have hp := continuous_pathHeatClockProfile_family c hc
  have hF : Continuous (fun x : ((Z × (Fin L × I)) × (Fin L × I)) =>
      pathHeatClockProfile (c x.1.1) (x.1.2.1,min x.1.2.2 x.2.2)) :=
    continuous_eval.comp ((hp.comp continuous_fst.fst).prodMk
      (continuous_fst.snd.fst.prodMk (continuous_fst.snd.snd.min continuous_snd.snd)))
  convert hD.mul hF using 1
  funext v
  rcases v with ⟨⟨z,x⟩,y⟩
  change pathHeatClockRawKernel (c z) x y =
    (if x.1=y.1 then 1 else 0) * c z x.1 (min x.2 y.2)
  rw [pathHeatClockRawKernel_apply]
  split_ifs <;> simp

theorem norm_pathHeatClockProfile_le_sum {L : ℕ} (c : Fin L → C(I,ℝ)) :
    ‖pathHeatClockProfile c‖ ≤ ∑l : Fin L, ‖c l‖ := by
  apply (ContinuousMap.norm_le _ (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).mpr
  intro x
  exact ((c x.1).norm_coe_le_norm x.2).trans
    (Finset.single_le_sum (fun l _ => norm_nonneg (c l)) (Finset.mem_univ x.1))

theorem norm_pathHeatClockRawKernel_le_sum {L : ℕ} (c : Fin L → C(I,ℝ)) :
    ‖pathHeatClockRawKernel c‖ ≤ ∑l : Fin L, ‖c l‖ :=
  (norm_pathHeatClockRawKernel_le c).trans (norm_pathHeatClockProfile_le_sum c)

end HexagonPaper
