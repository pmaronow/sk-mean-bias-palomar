module
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Operator.Basic

@[expose] public section

/-! Finite convex sampling of continuous paths. Bernstein sampling is used in
place of polygonal sampling: its coefficients are nonnegative, sum to one,
preserve both edge endpoints, and converge in the actual supremum norm. Thus
finite sampling never discretizes the signed derivative measures. -/
noncomputable section
open Set Filter
open scoped unitInterval Topology BigOperators
namespace HexagonPaper
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_bernsteinApproximation_le (n : ℕ) (f : C(I,E)) :
    ‖bernsteinApproximation n f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro x
  rw [bernsteinApproximation.apply]
  calc
    ‖∑i : Fin (n+1),bernstein n i x • f (bernstein.z i)‖
      ≤ ∑i : Fin (n+1),‖bernstein n i x • f (bernstein.z i)‖ := norm_sum_le _ _
    _ = ∑i : Fin (n+1),bernstein n i x*‖f (bernstein.z i)‖ := by
      congr 1;ext i;rw [norm_smul,Real.norm_of_nonneg bernstein_nonneg]
    _ ≤ ∑i : Fin (n+1),bernstein n i x*‖f‖ := by
      exact Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) bernstein_nonneg)
    _ = ‖f‖ := by rw [← Finset.sum_mul,bernstein.probability,one_mul]

/-- The finite path interpolation is a genuine bounded linear operator. -/
def bernsteinPathOperator (n : ℕ) : C(I,E) →L[ℝ] C(I,E) :=
  LinearMap.mkContinuous
    { toFun := bernsteinApproximation n
      map_add' := by
        intro f g;ext x
        simp only [bernsteinApproximation.apply,ContinuousMap.add_apply,smul_add,
          Finset.sum_add_distrib]
      map_smul' := by
        intro c f;ext x
        simp only [bernsteinApproximation.apply,ContinuousMap.smul_apply,
          RingHom.id_apply,Finset.smul_sum,smul_smul]
        congr 1;ext i;rw [mul_comm] }
    1 (by intro f;simpa using norm_bernsteinApproximation_le n f)

@[simp] theorem bernsteinPathOperator_apply (n : ℕ) (f : C(I,E)) :
    bernsteinPathOperator n f=bernsteinApproximation n f := rfl

theorem norm_bernsteinPathOperator_le (n : ℕ) :
    ‖bernsteinPathOperator (E:=E) n‖ ≤ 1 := by
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun f => by simpa using norm_bernsteinApproximation_le n f)

theorem bernsteinPathOperator_preserves_root (n : ℕ) (f : C(I,E)) :
    bernsteinPathOperator n f 0=f 0 := bernsteinApproximation.apply_zero _ _

theorem bernsteinPathOperator_preserves_terminal (n : ℕ) (hn : n≠0) (f : C(I,E)) :
    bernsteinPathOperator n f 1=f 1 := bernsteinApproximation.apply_one hn f

theorem tendsto_bernsteinPathOperator (f : C(I,E)) :
    Tendsto (fun n => bernsteinPathOperator n f) atTop (𝓝 f) :=
  bernsteinApproximation_uniform f

/-- A joint continuous family is approximated uniformly in its parameter as
well as its path argument, by applying Bernstein to a continuous-map codomain.
This is stronger than convergence separately at each parameter. -/
theorem tendsto_bernsteinPathOperator_joint {Z : Type*} [TopologicalSpace Z]
    [CompactSpace Z] (f : C(I,C(Z,E))) :
    Tendsto (fun n => bernsteinPathOperator n f) atTop (𝓝 f) :=
  tendsto_bernsteinPathOperator f

end HexagonPaper
