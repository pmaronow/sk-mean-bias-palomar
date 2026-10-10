module
public import HexagonPaper.PathHeatBernstein

@[expose] public section

/-! Actual double finite sampling of continuous covariance kernels. The same
construction applies to the covariance derivative and to joint parameter
families by taking a continuous-map codomain. No covariance inverse appears.
-/
noncomputable section
open Set Filter
open scoped unitInterval Topology BigOperators
namespace HexagonPaper
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def pathKernelTranspose (K : C(I,C(I,E))) : C(I,C(I,E)) :=
  (K.uncurry.comp ⟨Prod.swap,continuous_swap⟩).curry

@[simp] theorem pathKernelTranspose_apply (K : C(I,C(I,E))) (x y : I) :
    pathKernelTranspose K x y=K y x := rfl

@[simp] theorem pathKernelTranspose_involutive (K : C(I,C(I,E))) :
    pathKernelTranspose (pathKernelTranspose K)=K := by ext x y;rfl

theorem norm_pathKernelTranspose_le (K : C(I,C(I,E))) :
    ‖pathKernelTranspose K‖≤‖K‖ := by
  apply (ContinuousMap.norm_le (pathKernelTranspose K) (norm_nonneg K)).mpr
  intro x
  apply (ContinuousMap.norm_le (pathKernelTranspose K x) (norm_nonneg K)).mpr
  intro y
  exact ((K y).norm_coe_le_norm x).trans (K.norm_coe_le_norm y)

def pathKernelTransposeCLM : C(I,C(I,E)) →L[ℝ] C(I,C(I,E)) :=
  LinearMap.mkContinuous
    { toFun := pathKernelTranspose
      map_add' := by intro f g;ext x y;rfl
      map_smul' := by intro c f;ext x y;rfl }
    1 (by intro K;simpa using norm_pathKernelTranspose_le K)

def pathKernelRightSample (n : ℕ) : C(I,C(I,E)) →L[ℝ] C(I,C(I,E)) :=
  pathKernelTransposeCLM.comp ((bernsteinPathOperator n).comp pathKernelTransposeCLM)

@[simp] theorem pathKernelRightSample_apply (n : ℕ) (K : C(I,C(I,E))) :
    pathKernelRightSample n K = pathKernelTranspose
      (bernsteinApproximation n (pathKernelTranspose K)) := rfl

theorem norm_pathKernelRightSample_le (n : ℕ) (K : C(I,C(I,E))) :
    ‖pathKernelRightSample n K‖≤‖K‖ :=
  (norm_pathKernelTranspose_le _).trans
    ((norm_bernsteinApproximation_le _ _).trans (norm_pathKernelTranspose_le _))

theorem tendsto_pathKernelRightSample (K : C(I,C(I,E))) :
    Tendsto (fun n=>pathKernelRightSample n K) atTop (𝓝 K) := by
  have h := pathKernelTransposeCLM.continuous.continuousAt.tendsto.comp
    (tendsto_bernsteinPathOperator (pathKernelTranspose K))
  simpa only [bernsteinPathOperator_apply,pathKernelRightSample_apply,
    show (pathKernelTransposeCLM : C(I,C(I,E))→C(I,C(I,E)))=pathKernelTranspose from rfl,
    pathKernelTranspose_involutive,Function.comp_def] using h

/-- The genuine two-coordinate interpolated covariance kernel. -/
def pathKernelSample (n : ℕ) (K : C(I,C(I,E))) : C(I,C(I,E)) :=
  bernsteinPathOperator n (pathKernelRightSample n K)

theorem pathKernelSample_apply (n : ℕ) (K : C(I,C(I,E))) (x y : I) :
    pathKernelSample n K x y =
      ∑i : Fin (n+1),∑j : Fin (n+1),
        (bernstein n i x*bernstein n j y) • K (bernstein.z i) (bernstein.z j) := by
  simp only [pathKernelSample,bernsteinPathOperator_apply,bernsteinApproximation.apply,
    ContinuousMap.sum_apply,ContinuousMap.smul_apply,pathKernelRightSample_apply,
    pathKernelTranspose_apply,Finset.smul_sum,smul_smul]

theorem norm_pathKernelSample_le (n : ℕ) (K : C(I,C(I,E))) :
    ‖pathKernelSample n K‖≤‖K‖ :=
  (norm_bernsteinApproximation_le _ _).trans (norm_pathKernelRightSample_le _ _)

theorem pathKernel_norm_sub_tendsto_zero_of_tendsto
    (F : ℕ → C(I,C(I,E))) (K : C(I,C(I,E)))
    (hF : Tendsto F atTop (𝓝 K)) :
    Tendsto (fun n => ‖F n-K‖) atTop (𝓝 0) := by
  have hu := ContinuousMap.tendsto_iff_tendstoUniformly.mp hF
  have hm := Metric.tendstoUniformly_iff.mp hu
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact .of_forall fun n => ha.trans_le (norm_nonneg (F n-K))
  · intro a ha
    filter_upwards [hm a ha] with n hn
    apply (ContinuousMap.norm_lt_iff _ ha).mpr
    intro x
    have hx : dist (F n x) (K x) < a := (dist_comm _ _).trans_lt (hn x)
    simpa only [ContinuousMap.sub_apply, dist_eq_norm] using hx

theorem tendsto_pathKernelSample (K : C(I,C(I,E))) :
    Tendsto (fun n=>pathKernelSample n K) atTop (𝓝 K) := by
  have hr := pathKernel_norm_sub_tendsto_zero_of_tendsto
    (fun n => pathKernelRightSample n K) K (tendsto_pathKernelRightSample K)
  have hl := pathKernel_norm_sub_tendsto_zero_of_tendsto
    (fun n => bernsteinPathOperator n K) K (tendsto_bernsteinPathOperator K)
  have hbound (n : ℕ) : ‖pathKernelSample n K-K‖ ≤
      ‖pathKernelRightSample n K-K‖+‖bernsteinPathOperator n K-K‖ := by
    have he : pathKernelSample n K-K =
        bernsteinPathOperator n (pathKernelRightSample n K-K)+(bernsteinPathOperator n K-K) := by
      rw [map_sub];simp only [pathKernelSample];abel
    rw [he]
    exact (norm_add_le _ _).trans
      (add_le_add (norm_bernsteinApproximation_le _ _) le_rfl)
  rw [ContinuousMap.tendsto_iff_tendstoUniformly, Metric.tendstoUniformly_iff]
  intro ε hε
  have ht : Tendsto (fun n=>‖pathKernelRightSample n K-K‖+‖bernsteinPathOperator n K-K‖)
      atTop (𝓝 0) := by simpa only [zero_add] using hr.add hl
  filter_upwards [ht.eventually (Iio_mem_nhds hε)] with n hn x
  have hh := ((pathKernelSample n K-K).norm_coe_le_norm x).trans
    (hbound n) |>.trans_lt hn
  rw [dist_comm, dist_eq_norm]
  simpa only [ContinuousMap.sub_apply] using hh

end HexagonPaper
