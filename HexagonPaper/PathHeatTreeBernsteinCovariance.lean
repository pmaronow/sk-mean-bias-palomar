module
public import HexagonPaper.PathHeatTreeBernstein

@[expose] public section

/-! Double level sampling for finite edge-indexed covariance kernels. Edge
indices are never averaged, and signed covariance measures are retained. -/
noncomputable section
open Set Filter MeasureTheory
open scoped unitInterval Topology BigOperators BoundedContinuousFunction
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def pathHeatTreeKernelTranspose {L : ℕ} (K : C(Fin L × I,C(Fin L × I,E))) :
    C(Fin L × I,C(Fin L × I,E)) :=
  (K.uncurry.comp ⟨Prod.swap,continuous_swap⟩).curry

@[simp] theorem pathHeatTreeKernelTranspose_apply {L : ℕ}
    (K : C(Fin L × I,C(Fin L × I,E))) (x y : Fin L × I) :
    pathHeatTreeKernelTranspose K x y = K y x := rfl

@[simp] theorem pathHeatTreeKernelTranspose_involutive {L : ℕ}
    (K : C(Fin L × I,C(Fin L × I,E))) :
    pathHeatTreeKernelTranspose (pathHeatTreeKernelTranspose K) = K := by ext x y; rfl

theorem norm_pathHeatTreeKernelTranspose_le {L : ℕ}
    (K : C(Fin L × I,C(Fin L × I,E))) : ‖pathHeatTreeKernelTranspose K‖ ≤ ‖K‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg K)).mpr
  intro x
  apply (ContinuousMap.norm_le _ (norm_nonneg K)).mpr
  intro y
  exact ((K y).norm_coe_le_norm x).trans (K.norm_coe_le_norm y)

def pathHeatTreeKernelTransposeCLM (L : ℕ) :
    C(Fin L × I,C(Fin L × I,E)) →L[ℝ] C(Fin L × I,C(Fin L × I,E)) :=
  LinearMap.mkContinuous
    { toFun := pathHeatTreeKernelTranspose (L:=L) (E:=E)
      map_add' := by intro f g; ext x y; rfl
      map_smul' := by intro c f; ext x y; rfl }
    1 (by intro K; simpa using norm_pathHeatTreeKernelTranspose_le K)

def pathHeatTreeKernelRightSample (n L : ℕ) :
    C(Fin L × I,C(Fin L × I,E)) →L[ℝ] C(Fin L × I,C(Fin L × I,E)) :=
  (pathHeatTreeKernelTransposeCLM L).comp
    ((pathHeatTreeBernsteinOperator n L).comp (pathHeatTreeKernelTransposeCLM L))

@[simp] theorem pathHeatTreeKernelRightSample_apply (n L : ℕ)
    (K : C(Fin L × I,C(Fin L × I,E))) :
    pathHeatTreeKernelRightSample n L K = pathHeatTreeKernelTranspose
      (pathHeatTreeBernsteinSample n L (pathHeatTreeKernelTranspose K)) := rfl

theorem norm_pathHeatTreeKernelRightSample_le (n L : ℕ)
    (K : C(Fin L × I,C(Fin L × I,E))) :
    ‖pathHeatTreeKernelRightSample n L K‖ ≤ ‖K‖ :=
  (norm_pathHeatTreeKernelTranspose_le _).trans
    ((norm_pathHeatTreeBernsteinSample_le _ _ _).trans (norm_pathHeatTreeKernelTranspose_le _))

theorem tendsto_pathHeatTreeKernelRightSample (L : ℕ)
    (K : C(Fin L × I,C(Fin L × I,E))) :
    Tendsto (fun n => pathHeatTreeKernelRightSample n L K) atTop (𝓝 K) := by
  have h := (pathHeatTreeKernelTransposeCLM L).continuous.continuousAt.tendsto.comp
    (tendsto_pathHeatTreeBernsteinOperator L (pathHeatTreeKernelTranspose K))
  simpa only [pathHeatTreeBernsteinOperator_apply,pathHeatTreeKernelRightSample_apply,
    show (pathHeatTreeKernelTransposeCLM L : C(Fin L × I,C(Fin L × I,E)) →
      C(Fin L × I,C(Fin L × I,E))) = pathHeatTreeKernelTranspose from rfl,
    pathHeatTreeKernelTranspose_involutive,Function.comp_def] using h

def pathHeatTreeKernelSample (n L : ℕ) (K : C(Fin L × I,C(Fin L × I,E))) :
    C(Fin L × I,C(Fin L × I,E)) :=
  pathHeatTreeBernsteinOperator n L (pathHeatTreeKernelRightSample n L K)

theorem pathHeatTreeKernelSample_apply (n L : ℕ)
    (K : C(Fin L × I,C(Fin L × I,E))) (x y : Fin L × I) :
    pathHeatTreeKernelSample n L K x y =
      ∑i : Fin (n+1), ∑j : Fin (n+1),
        (bernstein n i x.2 * bernstein n j y.2) •
          K (x.1,bernstein.z i) (y.1,bernstein.z j) := by
  simp only [pathHeatTreeKernelSample,pathHeatTreeBernsteinOperator_apply,
    pathHeatTreeBernsteinSample_apply,ContinuousMap.sum_apply,ContinuousMap.smul_apply,
    pathHeatTreeKernelRightSample_apply,pathHeatTreeKernelTranspose_apply,
    Finset.smul_sum,smul_smul]

theorem norm_pathHeatTreeKernelSample_le (n L : ℕ)
    (K : C(Fin L × I,C(Fin L × I,E))) : ‖pathHeatTreeKernelSample n L K‖ ≤ ‖K‖ :=
  (norm_pathHeatTreeBernsteinSample_le _ _ _).trans (norm_pathHeatTreeKernelRightSample_le _ _ _)

theorem pathHeatTreeKernel_norm_sub_tendsto_zero_of_tendsto (L : ℕ)
    (F : ℕ → C(Fin L × I,C(Fin L × I,E))) (K : C(Fin L × I,C(Fin L × I,E)))
    (hF : Tendsto F atTop (𝓝 K)) :
    Tendsto (fun n => ‖F n-K‖) atTop (𝓝 0) := by
  have hm := Metric.tendstoUniformly_iff.mp (ContinuousMap.tendsto_iff_tendstoUniformly.mp hF)
  apply tendsto_order.mpr
  constructor
  · intro a ha; exact .of_forall fun n => ha.trans_le (norm_nonneg (F n-K))
  · intro a ha
    filter_upwards [hm a ha] with n hn
    apply (ContinuousMap.norm_lt_iff _ ha).mpr
    intro x
    have hx : dist (F n x) (K x) < a := (dist_comm _ _).trans_lt (hn x)
    simpa only [ContinuousMap.sub_apply,dist_eq_norm] using hx

theorem tendsto_pathHeatTreeKernelSample (L : ℕ)
    (K : C(Fin L × I,C(Fin L × I,E))) :
    Tendsto (fun n => pathHeatTreeKernelSample n L K) atTop (𝓝 K) := by
  have hr := pathHeatTreeKernel_norm_sub_tendsto_zero_of_tendsto L
    (fun n => pathHeatTreeKernelRightSample n L K) K (tendsto_pathHeatTreeKernelRightSample L K)
  have hl := pathHeatTreeKernel_norm_sub_tendsto_zero_of_tendsto L
    (fun n => pathHeatTreeBernsteinOperator n L K) K (tendsto_pathHeatTreeBernsteinOperator L K)
  have hb (n : ℕ) : ‖pathHeatTreeKernelSample n L K-K‖ ≤
      ‖pathHeatTreeKernelRightSample n L K-K‖ + ‖pathHeatTreeBernsteinOperator n L K-K‖ := by
    have he : pathHeatTreeKernelSample n L K-K =
        pathHeatTreeBernsteinOperator n L (pathHeatTreeKernelRightSample n L K-K) +
          (pathHeatTreeBernsteinOperator n L K-K) := by
      rw [map_sub]; simp only [pathHeatTreeKernelSample]; abel
    rw [he]
    exact (norm_add_le _ _).trans
      (add_le_add (norm_pathHeatTreeBernsteinSample_le n L
        (pathHeatTreeKernelRightSample n L K-K)) le_rfl)
  rw [ContinuousMap.tendsto_iff_tendstoUniformly,Metric.tendstoUniformly_iff]
  intro ε hε
  have ht : Tendsto (fun n => ‖pathHeatTreeKernelRightSample n L K-K‖ +
      ‖pathHeatTreeBernsteinOperator n L K-K‖) atTop (𝓝 0) := by
    simpa only [zero_add] using hr.add hl
  filter_upwards [ht.eventually (Iio_mem_nhds hε)] with n hn x
  have hh := ((pathHeatTreeKernelSample n L K-K).norm_coe_le_norm x).trans (hb n) |>.trans_lt hn
  rw [dist_comm,dist_eq_norm]
  simpa only [ContinuousMap.sub_apply] using hh

end HexagonPaper
