module
public import QuantitativePaper.VectorFiniteHessianStrict
public import QuantitativePaper.VectorHeatCalculus
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

/-! Actual terminal linear growth and finite Cole--Hopf coercivity. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

/-- Positive-mass smoothing dominates the value of a convex terminal. -/
theorem vectorColeHopfStep_ge_of_convex {n : ℕ} (f : Field n→ℝ) (K : ℝ≥0)
    (hf : LipschitzWith K f) (hconv : ConvexOn ℝ univ f) (c m : ℝ) (hm : 0 ≤ m) (x : Field n) :
    f x ≤ vectorColeHopfStep c m f x := by
  have hzi : Integrable (fun z : Field n=>z) (fieldGaussian n):=IsGaussian.integrable_id
  have hsi : Integrable (fieldShift c x) (fieldGaussian n):=
    (integrable_const x).add (hzi.smul (Real.sqrt c))
  have hs' : Integrable (fun z : Field n=>Real.sqrt c • z) (fieldGaussian n):=by
    convert hsi.sub (integrable_const x) using 1
    ext z
    simp [fieldShift]
  have he : (∫z,fieldShift c x z ∂fieldGaussian n)=x:=by
    change (∫z,x+Real.sqrt c • z ∂fieldGaussian n)=x
    rw [integral_add (integrable_const x) hs',integral_const,
      integral_smul]
    have hiz : (∫z : Field n,z ∂fieldGaussian n)=0:=by
      simpa only [fieldGaussian,id_eq] using
        (SYK.standardGaussianMeasureOnEuclidean_integral_id (ι:=Fin n))
    rw [hiz]
    simp
  have hFi:=integrable_vectorStep_input f K hf c x
  have hJ:=hconv.map_integral_le hf.continuous.continuousOn isClosed_univ
    (.of_forall fun _=>mem_univ _) hsi hFi
  rw [he] at hJ
  by_cases hm0:m=0
  · simpa only [vectorColeHopfStep,hm0,ite_true] using hJ
  · have hmp:0 < m:=lt_of_le_of_ne hm (Ne.symm hm0)
    have hEx:=convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
      (.of_forall fun _=>mem_univ _) (hFi.const_mul m) (integrable_exp_vectorStep f K hf c m x)
    rw [integral_const_mul] at hEx
    have hlog:=Real.log_le_log (Real.exp_pos _) hEx
    rw [Real.log_exp] at hlog
    unfold vectorColeHopfStep
    rw [ite_eq_right hm0]
    apply hJ.trans
    exact (le_div_iff₀ hmp).mpr (by simpa only [mul_comm,vectorStepPartition] using hlog)

theorem convexOn_vectorRecursion_field {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) : ConvexOn ℝ univ (vectorRecursion s β t p j) := by
  have hc:=convexOn_vectorRecursion_joint (n:=n) s β t j
  let A:Field n→ᵃ[ℝ]VectorParameter n:=(AffineMap.const ℝ (Field n) p).prod (AffineMap.id ℝ (Field n))
  simpa only [Function.comp_def,A,preimage_univ,AffineMap.prod_apply,AffineMap.const_apply,AffineMap.id_apply] using hc.comp_affineMap A

theorem vectorRecursion_ge_terminal {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) (x : Field n) :
    vectorTerminalPotential n β t p x ≤ vectorRecursion s β t p j x := by
  induction j generalizing x with
  | zero => exact le_rfl
  | succ j ih =>
    exact (ih x).trans (vectorColeHopfStep_ge_of_convex _ _ (vectorRecursion_lipschitz s β t p j)
      (convexOn_vectorRecursion_field s β t p j) _ _ (s.m_nonneg (Nat.sub_le _ _)) x)

theorem terminalPotential_ge_spin {n : ℕ} (E : Configuration n→ℝ) (σ : Configuration n) :
    E σ ≤ terminalPotential E := by
  have hs : Real.exp (E σ) ≤ terminalPartition E:=
    Finset.single_le_sum (fun τ _=>(Real.exp_pos _).le) (Finset.mem_univ σ)
  have hh:=Real.log_le_log (Real.exp_pos _) hs
  simpa only [Real.log_exp,terminalPotential] using hh

def vectorTerminalDisorderBound (n : ℕ) (β t : ℝ) (p : Couplings n×ℝ) : ℝ:=
  ∑σ : Configuration n,|β*Real.sqrt t*(energy n p.1 σ+p.2)|

theorem vectorTerminalPotential_l1_lower (n : ℕ) (β t : ℝ) (p : Couplings n×ℝ) (x : Field n) :
    (∑i : Fin n,|x i|)-vectorTerminalDisorderBound n β t p ≤ vectorTerminalPotential n β t p x := by
  classical
  let σ:Configuration n:=fun i=>decide (0 ≤ x i)
  have he:fieldDot x σ=∑i : Fin n,|x i|:=by
    unfold fieldDot
    apply Finset.sum_congr rfl
    intro i _
    by_cases hx:0 ≤ x i
    · simp [σ,hx,Paper.spinSign,abs_of_nonneg hx]
    · simp [σ,hx,Paper.spinSign,abs_of_neg (lt_of_not_ge hx)]
  have hB:|β*Real.sqrt t*(energy n p.1 σ+p.2)| ≤ vectorTerminalDisorderBound n β t p:=by
    unfold vectorTerminalDisorderBound
    exact Finset.single_le_sum (f:=fun τ : Configuration n=>|β*Real.sqrt t*(energy n p.1 τ+p.2)|)
      (fun τ _=>abs_nonneg _) (Finset.mem_univ σ)
  have hh:=terminalPotential_ge_spin (vectorTerminalExponent n β t p x) σ
  unfold vectorTerminalExponent at hh
  rw [he] at hh
  change _ ≤ terminalPotential (vectorTerminalExponent n β t p x)
  unfold vectorTerminalExponent
  linarith [neg_abs_le (β*Real.sqrt t*(energy n p.1 σ+p.2))]

theorem vectorRecursion_l1_lower {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) (x : Field n) :
    (∑i : Fin n,|x i|)-vectorTerminalDisorderBound n β t p ≤ vectorRecursion s β t p j x :=
  (vectorTerminalPotential_l1_lower n β t p x).trans (vectorRecursion_ge_terminal s β t p j x)

end QuantitativePaper
