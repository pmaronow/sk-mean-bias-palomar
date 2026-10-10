module
public import HexagonPaper.PathHeatBernsteinContraction

@[expose] public section

/-! Genuine finite coordinate sampling of finitely many continuous edges.
The edge index stays discrete; interpolation acts only on the level variable.
No derivative measure, including its endpoint atoms, is discretized. -/
noncomputable section
open Set Filter MeasureTheory
open scoped unitInterval Topology BigOperators BoundedContinuousFunction
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def pathHeatTreeEdge {L : ℕ} (f : C(Fin L × I,E)) (l : Fin L) : C(I,E) :=
  f.comp ⟨fun x => (l,x), continuous_const.prodMk continuous_id⟩

@[simp] theorem pathHeatTreeEdge_apply {L : ℕ} (f : C(Fin L × I,E))
    (l : Fin L) (x : I) : pathHeatTreeEdge f l x = f (l,x) := rfl

def pathHeatTreeBernsteinSample (n L : ℕ) (f : C(Fin L × I,E)) : C(Fin L × I,E) :=
  ⟨fun x => bernsteinPathOperator n (pathHeatTreeEdge f x.1) x.2,
    continuous_prod_of_discrete_left.mpr (fun l =>
      (bernsteinPathOperator n (pathHeatTreeEdge f l)).continuous)⟩

theorem pathHeatTreeBernsteinSample_apply (n L : ℕ) (f : C(Fin L × I,E))
    (x : Fin L × I) : pathHeatTreeBernsteinSample n L f x =
      ∑i : Fin (n+1), bernstein n i x.2 • f (x.1,bernstein.z i) := by
  exact bernsteinApproximation.apply n (pathHeatTreeEdge f x.1) x.2

theorem norm_pathHeatTreeBernsteinSample_le (n L : ℕ) (f : C(Fin L × I,E)) :
    ‖pathHeatTreeBernsteinSample n L f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro x
  have he : ‖pathHeatTreeEdge f x.1‖ ≤ ‖f‖ :=
    (ContinuousMap.norm_le _ (norm_nonneg f)).mpr (fun t => f.norm_coe_le_norm (x.1,t))
  exact ((bernsteinPathOperator n (pathHeatTreeEdge f x.1)).norm_coe_le_norm x.2).trans
    ((norm_bernsteinApproximation_le _ _).trans he)

def pathHeatTreeBernsteinOperator (n L : ℕ) : C(Fin L × I,E) →L[ℝ] C(Fin L × I,E) :=
  LinearMap.mkContinuous
    { toFun := pathHeatTreeBernsteinSample n L
      map_add' := by
        intro f g; ext x
        simp only [pathHeatTreeBernsteinSample_apply,ContinuousMap.add_apply,
          smul_add,Finset.sum_add_distrib]
      map_smul' := by
        intro c f; ext x
        simp only [pathHeatTreeBernsteinSample_apply,ContinuousMap.smul_apply,
          RingHom.id_apply,Finset.smul_sum,smul_smul]
        congr 1; ext i; rw [mul_comm] }
    1 (by intro f; simpa using norm_pathHeatTreeBernsteinSample_le n L f)

@[simp] theorem pathHeatTreeBernsteinOperator_apply (n L : ℕ) (f : C(Fin L × I,E)) :
    pathHeatTreeBernsteinOperator n L f = pathHeatTreeBernsteinSample n L f := rfl

theorem norm_pathHeatTreeBernsteinOperator_le (n L : ℕ) :
    ‖pathHeatTreeBernsteinOperator (E:=E) n L‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun f => by simpa using norm_pathHeatTreeBernsteinSample_le n L f)

theorem pathHeatTreeBernsteinOperator_preserves_root (n L : ℕ)
    (f : C(Fin L × I,E)) (l : Fin L) :
    pathHeatTreeBernsteinOperator n L f (l,0) = f (l,0) :=
  bernsteinPathOperator_preserves_root n (pathHeatTreeEdge f l)

theorem pathHeatTreeBernsteinOperator_preserves_terminal (n L : ℕ) (hn : n ≠ 0)
    (f : C(Fin L × I,E)) (l : Fin L) :
    pathHeatTreeBernsteinOperator n L f (l,1) = f (l,1) :=
  bernsteinPathOperator_preserves_terminal n hn (pathHeatTreeEdge f l)

theorem tendsto_pathHeatTreeBernsteinOperator (L : ℕ) (f : C(Fin L × I,E)) :
    Tendsto (fun n => pathHeatTreeBernsteinOperator n L f) atTop (𝓝 f) := by
  rw [ContinuousMap.tendsto_iff_tendstoUniformly, Metric.tendstoUniformly_iff]
  intro ε hε
  have he : ∀ l : Fin L, ∀ᶠ n in atTop,
      ∀ t : I, dist (pathHeatTreeEdge f l t)
        (bernsteinPathOperator n (pathHeatTreeEdge f l) t) < ε := by
    intro l
    exact (Metric.tendstoUniformly_iff.mp
      (ContinuousMap.tendsto_iff_tendstoUniformly.mp
        (tendsto_bernsteinPathOperator (pathHeatTreeEdge f l)))) ε hε
  filter_upwards [Filter.eventually_all.mpr he] with n hn x
  exact hn x.1 x.2

theorem tendsto_pathHeatTreeBernsteinOperator_joint {Z : Type*} [TopologicalSpace Z]
    [CompactSpace Z] (L : ℕ) (f : C(Fin L × I,C(Z,E))) :
    Tendsto (fun n => pathHeatTreeBernsteinOperator n L f) atTop (𝓝 f) :=
  tendsto_pathHeatTreeBernsteinOperator L f

def pathHeatTreeBernsteinBasis (n L : ℕ) (p : Fin L × Fin (n+1)) : C(Fin L × I,ℝ) :=
  ⟨fun x => if x.1 = p.1 then bernstein n p.2 x.2 else 0,
    continuous_prod_of_discrete_left.mpr (fun l => by
      by_cases h : l = p.1
      · simpa only [h,ite_true] using (bernstein n p.2).continuous
      · simpa only [h,ite_false] using (continuous_const : Continuous (fun _ : I => (0:ℝ))))⟩

@[simp] theorem pathHeatTreeBernsteinBasis_apply (n L : ℕ)
    (p : Fin L × Fin (n+1)) (x : Fin L × I) :
    pathHeatTreeBernsteinBasis n L p x = if x.1 = p.1 then bernstein n p.2 x.2 else 0 := rfl

def pathHeatTreeBernsteinSynthesis (n L : ℕ) :
    EuclideanSpace ℝ (Fin L × Fin (n+1)) →L[ℝ] C(Fin L × I,ℝ) :=
  ∑p : Fin L × Fin (n+1),
    (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin L × Fin (n+1) => ℝ) p).smulRight
      (pathHeatTreeBernsteinBasis n L p)

theorem pathHeatTreeBernsteinSynthesis_apply (n L : ℕ)
    (g : EuclideanSpace ℝ (Fin L × Fin (n+1))) (x : Fin L × I) :
    pathHeatTreeBernsteinSynthesis n L g x =
      ∑i : Fin (n+1), bernstein n i x.2 * g (x.1,i) := by
  simp only [pathHeatTreeBernsteinSynthesis,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply,PiLp.proj_apply,ContinuousMap.sum_apply,
    ContinuousMap.smul_apply,smul_eq_mul,pathHeatTreeBernsteinBasis_apply]
  rw [Fintype.sum_prod_type]
  simp only [mul_ite,mul_zero,Finset.sum_ite_irrel]
  simp [mul_comm]

theorem pathHeatTreeBernsteinSynthesis_basis (n L : ℕ) (p : Fin L × Fin (n+1)) :
    pathHeatTreeBernsteinSynthesis n L (EuclideanSpace.single p 1) =
      pathHeatTreeBernsteinBasis n L p := by
  simp [pathHeatTreeBernsteinSynthesis,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply,PiLp.proj_apply,PiLp.single_apply]

theorem norm_pathHeatTreeBernsteinSynthesis_le (n L : ℕ) :
    ‖pathHeatTreeBernsteinSynthesis n L‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro g
  simp only [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg g)).mpr
  intro x
  rw [pathHeatTreeBernsteinSynthesis_apply]
  calc
    ‖∑i : Fin (n+1),bernstein n i x.2*g (x.1,i)‖ ≤
      ∑i : Fin (n+1),‖bernstein n i x.2*g (x.1,i)‖ := norm_sum_le _ _
    _ = ∑i : Fin (n+1),bernstein n i x.2*‖g (x.1,i)‖ := by
      congr 1; ext i; rw [norm_mul,Real.norm_of_nonneg bernstein_nonneg]
    _ ≤ ∑i : Fin (n+1),bernstein n i x.2*‖g‖ :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (PiLp.norm_apply_le g (x.1,i)) bernstein_nonneg)
    _ = ‖g‖ := by rw [←Finset.sum_mul,bernstein.probability,one_mul]

def pathHeatTreeBernsteinEvaluation (n L : ℕ) :
    C(Fin L × I,ℝ) →L[ℝ] EuclideanSpace ℝ (Fin L × Fin (n+1)) where
  toFun f := WithLp.toLp 2 (fun p => f (p.1,bernstein.z p.2))
  map_add' f g := by ext p; rfl
  map_smul' c f := by ext p; rfl
  cont := (PiLp.continuous_toLp 2 (fun _ : Fin L × Fin (n+1) => ℝ)).comp
    (continuous_pi (fun p => continuous_eval_const (p.1,bernstein.z p.2)))

@[simp] theorem pathHeatTreeBernsteinEvaluation_apply (n L : ℕ)
    (f : C(Fin L × I,ℝ)) (p : Fin L × Fin (n+1)) :
    pathHeatTreeBernsteinEvaluation n L f p = f (p.1,bernstein.z p.2) := rfl

theorem pathHeatTreeBernsteinSynthesis_evaluation (n L : ℕ) (f : C(Fin L × I,ℝ)) :
    pathHeatTreeBernsteinSynthesis n L (pathHeatTreeBernsteinEvaluation n L f) =
      pathHeatTreeBernsteinOperator n L f := by
  ext x
  rw [pathHeatTreeBernsteinSynthesis_apply,pathHeatTreeBernsteinOperator_apply,
    pathHeatTreeBernsteinSample_apply]
  rfl

end HexagonPaper
