module
public import QuantitativePaper.VectorProfilePosteriorScoreBound
public import QuantitativePaper.VectorHistoryLinear
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

/-! Genuine Gaussian exponential domination for the affine-profile posterior.
The retained field displacement is an actual continuous linear map of its
independent Gaussian coordinates. Bounds here justify differentiation at a
fixed finite mesh; the score constants themselves remain depth independent.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology NNReal ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorCoordinateUpdate_zero_noise (s : RSBScheme k) (β t : ℝ)
    (i : ℕ) (y : VectorState n) : vectorCoordinateUpdate s β t i y 0=y := by
  unfold vectorCoordinateUpdate vectorStateUpdate fieldShift
  split_ifs <;> simp

theorem independentHistory_zero_noise {State Noise : Type*} [Zero Noise]
    (u : ℕ→State→Noise→State) (hu : ∀i x,u i x 0=x) (N : ℕ) (x : State)
    (i : Fin (N+1)) : independentHistory u N (x,0) i=x := by
  induction N with
  | zero => rfl
  | succ N ih =>
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simp only [independentHistory,Fin.snoc_last]
      rw [show (fun j : Fin N => (0 : Fin (N+1)→Noise) j.castSucc)=0 by rfl,
        ih,show (0 : Fin (N+1)→Noise) (Fin.last N)=0 by rfl,hu]
    · simp only [independentHistory,Fin.snoc_castSucc]
      exact ih j

def vectorTailNoiseFieldHistoryLinear (s : RSBScheme k) (β t : ℝ) (L j : ℕ) :
    (Fin j→Field n)→L[ℝ](Fin (j+1)→Field n) :=
  (ContinuousLinearMap.pi fun i : Fin (j+1) =>
    (ContinuousLinearMap.snd ℝ (Couplings n×ℝ) (Field n)).comp
      (ContinuousLinearMap.proj i)).comp
    ((independentHistoryLinear (fun i=>vectorCoordinateUpdateLinear s β t (L+i)) j).comp
      (ContinuousLinearMap.inr ℝ (VectorState n) (Fin j→Field n)))

theorem vectorTailNoiseFieldHistoryLinear_apply (s : RSBScheme k) (β t : ℝ)
    (L j : ℕ) (p : Couplings n×ℝ) (x : Field n) (z : Fin j→Field n) :
    vectorTailNoiseFieldHistoryLinear s β t L j z=
      fun i=>(vectorHistoryFrom s β t L p x j z i).2-x := by
  let A:=independentHistoryLinear (fun i=>vectorCoordinateUpdateLinear (n:=n) s β t (L+i)) j
  have he : ∀ y : VectorState n,∀ w : Fin j→Field n,
      A (y,w)=independentHistory (fun i=>vectorCoordinateUpdate s β t (L+i)) j (y,w) := by
    intro y w
    rw [show A (y,w)=independentHistory (fun i a z=>
      vectorCoordinateUpdateLinear s β t (L+i) (a,z)) j (y,w) from
      independentHistoryLinear_apply _ _ _]
    simp_rw [vectorCoordinateUpdateLinear_apply]
  have ha : A ((p,x),z)=A ((p,x),0)+A (0,z) := by
    rw [←map_add]
    simp
  apply funext
  intro i
  have hh:=congrArg (fun h : Fin (j+1)→VectorState n=>(h i).2) ha
  change (A ((p,x),z) i).2=(A ((p,x),0) i).2+(A (0,z) i).2 at hh
  rw [he,he,independentHistory_zero_noise _
    (fun i y=>vectorCoordinateUpdate_zero_noise s β t (L+i) y)] at hh
  change (A (0,z) i).2=(vectorHistoryFrom s β t L p x j z i).2-x
  change (vectorHistoryFrom s β t L p x j z i).2=x+(A (0,z) i).2 at hh
  rw [hh]
  abel

theorem vectorProfilePosteriorFieldEnvelope_eq_norm_linear (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n×ℝ) (x : Field n) (N : ℕ) (z : Fin (N+1)→Field n) :
    vectorProfilePosteriorFieldEnvelope s β t p x N z=
      ‖vectorTailNoiseFieldHistoryLinear s β t (k+2-(N+1)) (N+1) z‖ := by
  rw [vectorTailNoiseFieldHistoryLinear_apply]
  rfl

theorem integrable_exp_pi_field_norm (n j : ℕ) (D : ℝ) :
    Integrable (fun z : Fin j→Field n=>Real.exp (D*‖z‖))
      (Measure.pi (fun _ : Fin j=>fieldGaussian n)) := by
  have hi : Integrable (fun z : Fin j→Field n=>
      Real.exp (|D| *∑i,‖z i‖)) (Measure.pi (fun _ : Fin j=>fieldGaussian n)) := by
    simpa only [Finset.mul_sum,Real.exp_sum] using
      Integrable.fintype_prod (fun _ : Fin j=>SYK.integrable_exp_mul_norm (ι:=Fin n) |D|)
  apply hi.mono' ((Real.continuous_exp.comp (continuous_const.mul continuous_norm)).measurable.aestronglyMeasurable)
  exact .of_forall fun z=>by
    dsimp only [Function.comp_def,Pi.mul_apply]
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hn : ‖z‖≤∑i,‖z i‖ := by
      apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _=>norm_nonneg _)).mpr
      intro i
      exact Finset.single_le_sum (fun _ _=>norm_nonneg _) (Finset.mem_univ i)
    exact (mul_le_mul_of_nonneg_right (le_abs_self D) (norm_nonneg z)).trans
      (mul_le_mul_of_nonneg_left hn (abs_nonneg D))

theorem measurable_vectorProfilePosteriorFieldEnvelope (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n×ℝ) (x : Field n) (N : ℕ) :
    Measurable (vectorProfilePosteriorFieldEnvelope s β t p x N) := by
  have he : vectorProfilePosteriorFieldEnvelope s β t p x N=
      fun z=>‖vectorTailNoiseFieldHistoryLinear s β t (k+2-(N+1)) (N+1) z‖ := by
    funext z
    exact vectorProfilePosteriorFieldEnvelope_eq_norm_linear s β t p x N z
  rw [he]
  exact (vectorTailNoiseFieldHistoryLinear s β t _ _).continuous.norm.measurable

theorem integrable_exp_vectorProfilePosteriorFieldEnvelope (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n×ℝ) (x : Field n) (N : ℕ) (D : ℝ) :
    Integrable (fun z : Fin (N+1)→Field n=>
      Real.exp (D*vectorProfilePosteriorFieldEnvelope s β t p x N z))
      (Measure.pi (fun _ : Fin (N+1)=>fieldGaussian n)) := by
  let A:=vectorTailNoiseFieldHistoryLinear (n:=n) s β t (k+2-(N+1)) (N+1)
  apply (integrable_exp_pi_field_norm n (N+1) (|D| *‖A‖)).mono'
    ((measurable_const.mul (measurable_vectorProfilePosteriorFieldEnvelope s β t p x N)).exp.aestronglyMeasurable)
  exact .of_forall fun z=>by
    dsimp only [Pi.mul_apply]
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),vectorProfilePosteriorFieldEnvelope_eq_norm_linear]
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_right (le_abs_self D) (norm_nonneg (A z))).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (A.le_opNorm z) (abs_nonneg D))

end QuantitativePaper
