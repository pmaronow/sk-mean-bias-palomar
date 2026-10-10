module
public import QuantitativePaper.VectorFieldConditionalVariance
public import QuantitativePaper.VectorTerminalStrict
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

/-! Positive definiteness of the actual finite vector potential Hessian.
Strict terminal spin variance is propagated through genuine normalized
Gaussian expectations, including zero masses and zero variances. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem terminalCovariance_self_pos {n : ℕ} (E b : Configuration n→ℝ)
    (hb : ∃σ τ,b σ ≠ b τ) : 0 < terminalCovariance E b b := by
  classical
  obtain ⟨σ,τ,hst⟩:=hb
  have he : ∃v,b v ≠ terminalMean E b:=by
    by_contra h
    push_neg at h
    exact hst ((h σ).trans (h τ).symm)
  obtain ⟨v,hv⟩:=he
  rw [terminalCovariance_centered]
  unfold terminalMean
  apply Finset.sum_pos'
  · intro w _
    exact mul_nonneg (terminalWeight_pos E w).le (mul_self_nonneg _)
  · exact ⟨v,Finset.mem_univ v,mul_pos (terminalWeight_pos E v)
      (mul_self_pos.mpr (sub_ne_zero.mpr hv))⟩

theorem vectorStepResponse_pos {n : ℕ} (f v : Field n→ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (hv : Measurable v) (R : ℝ) (hB : ∀x,|v x| ≤ R)
    (hpos : ∀x,0 < v x) (c m : ℝ) (x : Field n) :
    0 < vectorStepResponse c m f v x := by
  have hi:=integrable_vectorStepResponse_input f v K hf hv R hB c m x
  unfold vectorStepResponse
  rw [integral_pos_iff_support_of_nonneg (fun z=>
    (mul_pos (vectorStepWeight_pos f K hf c m x z) (hpos _)).le) hi]
  have he : Function.support (fun z=>vectorStepWeight c m f x z*v (fieldShift c x z))=univ:=by
    ext z
    simp only [Function.mem_support,mem_univ,iff_true]
    exact (mul_pos (vectorStepWeight_pos f K hf c m x z) (hpos _)).ne'
  rw [he,measure_univ]
  exact zero_lt_one

theorem vectorObservableSecondResponse_pos {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (b : Configuration n→ℝ) (R : ℝ≥0)
    (hB : ∀σ,|b σ| ≤ R) (hb : ∃σ τ,b σ ≠ b τ) (j : ℕ) (y : ℝ) (x : Field n) :
    0 < vectorObservableSecondResponse s β t p b j y x := by
  induction j generalizing x with
  | zero => exact terminalCovariance_self_pos _ b hb
  | succ j ih =>
    let f:=vectorPerturbedRecursion s β t p b j y
    let v:=vectorObservableResponse s β t p b j y
    let H:=vectorObservableSecondResponse s β t p b j y
    let c:=(1-t)*(β^2*(s.q (k+2-j)-s.q (k+1-j)))
    let m:=s.m (k+1-j)
    have hf:=vectorPerturbedRecursion_lipschitz s β t p b j y
    have hH:Measurable H:=(measurable_vectorObservableSecondResponse s β t p b j).comp
      (measurable_const.prodMk measurable_id)
    have hv:Measurable v:=(measurable_vectorObservableResponse s β t p b j).comp
      (measurable_const.prodMk measurable_id)
    have hP:=vectorStepResponse_pos f H _ hf hH (observableSecondBound R j)
      (fun z=>abs_vectorObservableSecondResponse_le s β t p b R hB j y z) ih c m x
    have hV:=vectorStepResponse_variance_nonneg f v _ hf hv R
      (fun z=>abs_vectorObservableResponse_le s β t p b R hB j y z) c m x
    have hm:0 ≤ m:=s.m_nonneg (Nat.sub_le _ _)
    change 0 < vectorStepResponse c m f H x+m*(vectorStepResponse c m f (fun z=>v z^2) x-
      (vectorStepResponse c m f v x)^2)
    exact add_pos_of_pos_of_nonneg hP (mul_nonneg hm hV)

/-- A nonzero field direction is nonconstant on the literal binary spins. -/
theorem fieldDot_nonconstant {n : ℕ} (w : Field n) (hw : w ≠ 0) :
    ∃σ τ,fieldDot w σ ≠ fieldDot w τ := by
  classical
  have hi : ∃i : Fin n,w i ≠ 0:=by
    by_contra h
    push_neg at h
    apply hw
    ext i
    exact h i
  obtain ⟨i,hi⟩:=hi
  let σ:Configuration n:=fun _=>true
  let τ:Configuration n:=Function.update σ i false
  have hd : fieldDot w τ-fieldDot w σ= -2*w i:=by
    unfold fieldDot
    rw [←Finset.sum_sub_distrib]
    have he (j : Fin n) : w j*Paper.spinSign (τ j)-w j*Paper.spinSign (σ j)=
        if j=i then -2*w i else 0:=by
      by_cases hj:j=i
      · subst j
        simp [τ,σ,Paper.spinSign]
        ring
      · simp [τ,σ,Function.update_apply,hj,Paper.spinSign]
    simp_rw [he]
    simp
  refine ⟨τ,σ,?_⟩
  intro he
  rw [he,sub_self] at hd
  apply hi
  linarith

theorem vectorFieldHessian_quadratic_pos {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) (x w : Field n) (hw : w ≠ 0) :
    0 < inner ℝ w (vectorFieldHessian s β t p j x w) := by
  rw [vectorFieldHessian_quadratic_eq_secondResponse]
  let R:ℝ≥0:=(Real.sqrt (n : ℝ)*‖w‖).toNNReal
  have hB (σ : Configuration n):|fieldDot w σ| ≤ R:=by
    rw [show (R : ℝ)=Real.sqrt (n : ℝ)*‖w‖ from
      Real.coe_toNNReal _ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
    exact abs_fieldDot w σ
  exact vectorObservableSecondResponse_pos s β t p _ R hB (fieldDot_nonconstant w hw) j 0 x

theorem vectorFieldHessian_isUnit {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) (x : Field n) :
    IsUnit (vectorFieldHessian s β t p j x) := by
  let H:=vectorFieldHessian s β t p j x
  have hinj:Function.Injective H:=by
    apply (H.toLinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro w hw
    by_contra hne
    have hp:=vectorFieldHessian_quadratic_pos s β t p j x w hne
    change H w=0 at hw
    change 0 < inner ℝ w (H w) at hp
    rw [hw,inner_zero_right] at hp
    exact lt_irrefl 0 hp
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hinj,LinearMap.injective_iff_surjective.mp hinj⟩

end QuantitativePaper
