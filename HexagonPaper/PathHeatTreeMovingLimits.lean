module
public import HexagonPaper.PathHeatTreeBernsteinCovariance

@[expose] public section

/-! Moving-parameter Bernstein limits on the actual finite edge space.
All estimates use the unchanged path supremum norm. -/
noncomputable section
open Set Filter MeasureTheory
open scoped unitInterval Topology
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem pathHeat_continuousMap_norm_sub_tendsto_zero
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (f : ℕ→C(X,E)) (g : C(X,E)) (h : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun n=>‖f n-g‖) atTop (𝓝 0) := by
  have hu := Metric.tendstoUniformly_iff.mp (ContinuousMap.tendsto_iff_tendstoUniformly.mp h)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact .of_forall fun n=>ha.trans_le (norm_nonneg (f n-g))
  · intro a ha
    filter_upwards [hu a ha] with n hn
    apply (ContinuousMap.norm_lt_iff _ ha).mpr
    intro x
    have hx : dist (f n x) (g x)<a := (dist_comm _ _).trans_lt (hn x)
    simpa only [ContinuousMap.sub_apply,dist_eq_norm] using hx

theorem tendsto_pathHeatTreeBernsteinOperator_moving (L : ℕ)
    (f : ℕ→C(Fin L×I,E)) (g : C(Fin L×I,E))
    (hf : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun n=>pathHeatTreeBernsteinOperator n L (f n)) atTop (𝓝 g) := by
  have hleft := pathHeat_continuousMap_norm_sub_tendsto_zero f g hf
  have hright := pathHeat_continuousMap_norm_sub_tendsto_zero
    (fun n=>pathHeatTreeBernsteinOperator n L g) g (tendsto_pathHeatTreeBernsteinOperator L g)
  have ht : Tendsto (fun n=>‖f n-g‖+‖pathHeatTreeBernsteinOperator n L g-g‖) atTop (𝓝 0) := by
    simpa only [zero_add] using hleft.add hright
  have hb (n : ℕ) : ‖pathHeatTreeBernsteinOperator n L (f n)-g‖≤
      ‖f n-g‖+‖pathHeatTreeBernsteinOperator n L g-g‖ := by
    have he : pathHeatTreeBernsteinOperator n L (f n)-g=
        pathHeatTreeBernsteinOperator n L (f n-g)+(pathHeatTreeBernsteinOperator n L g-g) := by
      rw [map_sub];abel
    rw [he]
    exact (norm_add_le _ _).trans
      (add_le_add (norm_pathHeatTreeBernsteinSample_le n L (f n-g)) le_rfl)
  rw [ContinuousMap.tendsto_iff_tendstoUniformly,Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [ht.eventually (Iio_mem_nhds hε)] with n hn x
  have hh := ((pathHeatTreeBernsteinOperator n L (f n)-g).norm_coe_le_norm x).trans
    (hb n) |>.trans_lt hn
  rw [dist_comm,dist_eq_norm]
  simpa only [ContinuousMap.sub_apply] using hh

theorem tendsto_pathHeatTreeKernelSample_moving (L : ℕ)
    (K : ℕ→C(Fin L×I,C(Fin L×I,E))) (G : C(Fin L×I,C(Fin L×I,E)))
    (hK : Tendsto K atTop (𝓝 G)) :
    Tendsto (fun n=>pathHeatTreeKernelSample n L (K n)) atTop (𝓝 G) := by
  have hleft := pathHeatTreeKernel_norm_sub_tendsto_zero_of_tendsto L K G hK
  have hright := pathHeatTreeKernel_norm_sub_tendsto_zero_of_tendsto L
    (fun n=>pathHeatTreeKernelSample n L G) G (tendsto_pathHeatTreeKernelSample L G)
  have ht : Tendsto (fun n=>‖K n-G‖+‖pathHeatTreeKernelSample n L G-G‖) atTop (𝓝 0) := by
    simpa only [zero_add] using hleft.add hright
  have hb (n : ℕ) : ‖pathHeatTreeKernelSample n L (K n)-G‖≤
      ‖K n-G‖+‖pathHeatTreeKernelSample n L G-G‖ := by
    have he : pathHeatTreeKernelSample n L (K n)-G=
        pathHeatTreeBernsteinOperator n L
          (pathHeatTreeKernelRightSample n L (K n-G))+(pathHeatTreeKernelSample n L G-G) := by
      simp only [pathHeatTreeKernelSample,map_sub];abel
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add
      ((norm_pathHeatTreeBernsteinSample_le n L _).trans
        (norm_pathHeatTreeKernelRightSample_le n L (K n-G))) le_rfl)
  rw [ContinuousMap.tendsto_iff_tendstoUniformly,Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [ht.eventually (Iio_mem_nhds hε)] with n hn x
  have hh := ((pathHeatTreeKernelSample n L (K n)-G).norm_coe_le_norm x).trans
    (hb n) |>.trans_lt hn
  rw [dist_comm,dist_eq_norm]
  simpa only [ContinuousMap.sub_apply] using hh

end HexagonPaper
