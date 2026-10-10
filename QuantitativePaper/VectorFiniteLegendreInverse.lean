module
public import QuantitativePaper.VectorFiniteCoercivity
public import QuantitativePaper.VectorGradientBounds
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-! The literal finite-vector gradient map is onto the open spin cube.
The minimizing field is obtained by coercivity of the actual Cole--Hopf
potential, rather than assumed as a Legendre-coordinate premise. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators InnerProductSpace
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def vectorOpenSpinCube (n : ℕ) : Set (Field n) := {m | ∀i,|m i| < 1}

theorem field_inner_le_piNorm_l1 {n : ℕ} (m x : Field n) :
    inner ℝ m x ≤ ‖m.ofLp‖*(∑i : Fin n,|x i|) := by
  classical
  rw [PiLp.inner_apply]
  calc
    _ ≤ ∑i : Fin n,‖m.ofLp‖*|x i| := Finset.sum_le_sum fun i _ => by
      simp only [RCLike.inner_apply,conj_trivial]
      have hm : |m i| ≤ ‖m.ofLp‖:=by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm m.ofLp i
      calc
        _ ≤ |x i*m i|:=le_abs_self _
        _ = |m i| * |x i|:=by rw [abs_mul,mul_comm]
        _ ≤ _:=mul_le_mul_of_nonneg_right hm (abs_nonneg _)
    _ = _:=by rw [Finset.mul_sum]

theorem vectorRecursion_minus_field_coercive_lower {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n×ℝ) (j : ℕ) (m : Field n)
    (hm : m∈vectorOpenSpinCube n) (x : Field n) :
    (1-‖m.ofLp‖)*‖x‖-vectorTerminalDisorderBound n β t p ≤
      vectorRecursion s β t p j x-inner ℝ m x := by
  have hρ : ‖m.ofLp‖ < 1:= (pi_norm_lt_iff (by norm_num : (0 : ℝ)<1)).mpr
    (by simpa only [Real.norm_eq_abs,vectorOpenSpinCube,mem_setOf_eq] using hm)
  have hl : ‖x‖ ≤ ∑i : Fin n,|x i|:=by
    simpa only [WithLp.toLp_ofLp,l1] using norm_toLp_le_l1 x.ofLp
  have hg:=vectorRecursion_l1_lower s β t p j x
  have hi:=field_inner_le_piNorm_l1 m x
  have hs:=mul_le_mul_of_nonneg_left hl (sub_pos.mpr hρ).le
  nlinarith

theorem exists_vectorRecursion_minus_field_minimizer {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n×ℝ) (j : ℕ) (m : Field n)
    (hm : m∈vectorOpenSpinCube n) :
    ∃x : Field n,∀y : Field n,
      vectorRecursion s β t p j x-inner ℝ m x ≤
        vectorRecursion s β t p j y-inner ℝ m y := by
  let f:=fun x : Field n=>vectorRecursion s β t p j x-inner ℝ m x
  have hc:Continuous f:=(contDiff_vectorRecursion_field s β t p j).continuous.sub
    (continuous_const.inner continuous_id)
  have hρ : ‖m.ofLp‖ < 1:= (pi_norm_lt_iff (by norm_num : (0 : ℝ)<1)).mpr
    (by simpa only [Real.norm_eq_abs,vectorOpenSpinCube,mem_setOf_eq] using hm)
  have hδ:0 < 1-‖m.ofLp‖:=sub_pos.mpr hρ
  apply hc.exists_forall_le' 0
  filter_upwards [(tendsto_norm_cocompact_atTop (E:=Field n)).eventually
    (eventually_ge_atTop ((f 0+vectorTerminalDisorderBound n β t p)/(1-‖m.ofLp‖)))] with x hx
  have hh:=vectorRecursion_minus_field_coercive_lower s β t p j m hm x
  have he: f 0+vectorTerminalDisorderBound n β t p ≤ (1-‖m.ofLp‖)*‖x‖:=
    by simpa only [mul_comm] using (div_le_iff₀ hδ).mp hx
  dsimp only [f] at he ⊢
  nlinarith

theorem vectorMagnetization_surjective_openCube {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n×ℝ) (j : ℕ) (m : Field n)
    (hm : m∈vectorOpenSpinCube n) :
    ∃x : Field n,vectorMagnetization s β t p j x=m := by
  obtain ⟨x,hx⟩:=exists_vectorRecursion_minus_field_minimizer s β t p j m hm
  let L:Field n→L[ℝ]ℝ:=InnerProductSpace.toDual ℝ (Field n) m
  have hd:=((contDiff_vectorRecursion_field s β t p j).differentiable (by simp) x).hasFDerivAt
  have hmin:IsLocalMin (fun y : Field n=>vectorRecursion s β t p j y-L y) x:=
    .of_forall hx
  have hz:=hmin.hasFDerivAt_eq_zero (hd.sub L.hasFDerivAt)
  refine ⟨x,?_⟩
  ext i
  have he:=DFunLike.congr_fun hz (EuclideanSpace.single i (1 : ℝ))
  rw [ContinuousLinearMap.sub_apply,fderiv_vectorRecursion_coordinate] at he
  simp only [L,InnerProductSpace.toDual_apply_apply,EuclideanSpace.inner_single_right,
    ContinuousLinearMap.zero_apply,conj_trivial,mul_one,one_mul] at he
  linarith

theorem vectorMagnetization_injective {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n×ℝ) (j : ℕ) :
    Function.Injective (vectorMagnetization s β t p j) := by
  intro x y hxy
  by_contra hne
  let w:=y-x
  have hw:w ≠ 0:=sub_ne_zero.mpr (Ne.symm hne)
  let F:=vectorRecursion s β t p j
  have hF:ContDiff ℝ 2 F:=(contDiff_vectorRecursion_field s β t p j).of_le (by simp)
  have hd (r : ℝ) : HasDerivAt (fun a : ℝ=>inner ℝ w (gradient F (x+a • w)))
      (inner ℝ w (vectorFieldHessian s β t p j (x+r • w) w)) r:=by
    have hg:= (hasFDerivAt_gradient_hessianOperator F hF (x+r • w)).comp_hasDerivAt r
      ((hasDerivAt_id r).smul_const w |>.const_add x)
    simpa only [id_eq,Function.comp_def,one_smul,inner_zero_left,zero_add,add_zero,F,vectorFieldHessian] using
      (hasDerivAt_const r w).inner ℝ hg
  have hmono:=strictMono_of_hasDerivAt_pos hd
    (fun r=>vectorFieldHessian_quadratic_pos s β t p j (x+r • w) w hw)
  have hh:=hmono (by norm_num : (0 : ℝ)<1)
  have he:gradient F x=gradient F y:=by
    simpa only [F,←vectorMagnetization_eq_gradient] using hxy
  have hey:x+(1 : ℝ) • w=y:=by simp [w]
  simp only [zero_smul,add_zero,hey,he] at hh
  exact lt_irrefl _ hh

end QuantitativePaper
