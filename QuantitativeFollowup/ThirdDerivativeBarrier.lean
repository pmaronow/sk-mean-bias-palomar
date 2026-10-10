module
public import FRSB.BackwardsClassicalCell
public import Paper.Hyperbolic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic

@[expose] public section

/-! An explicit strict half-line barrier for the negative third derivative.
This elementary subsolution has no supplied positivity premise. -/
noncomputable section
open Set
open scoped ContDiff
namespace QuantitativeFollowup

def thirdDerivativeBarrier (p : ℝ×ℝ) : ℝ :=
  2*Real.exp (-4)*Real.exp (-4*p.1)*p.2*Real.exp (-p.2^2)

def thirdDerivativeBarrierX (p : ℝ×ℝ) : ℝ :=
  2*Real.exp (-4)*Real.exp (-4*p.1)*(1-2*p.2^2)*Real.exp (-p.2^2)

def thirdDerivativeBarrierXX (p : ℝ×ℝ) : ℝ :=
  2*Real.exp (-4)*Real.exp (-4*p.1)*(4*p.2^3-6*p.2)*Real.exp (-p.2^2)

@[fun_prop] theorem contDiff_thirdDerivativeBarrier : ContDiff ℝ ∞ thirdDerivativeBarrier := by
  unfold thirdDerivativeBarrier
  fun_prop

theorem hasDerivAt_thirdDerivativeBarrier_time (τ x : ℝ) :
    HasDerivAt (fun r=>thirdDerivativeBarrier (r,x)) (-4*thirdDerivativeBarrier (τ,x)) τ := by
  have he:=((hasDerivAt_id τ).const_mul (-4)).exp
  convert (((he.const_mul (2*Real.exp (-4))).mul_const x).mul_const (Real.exp (-x^2))) using 1 <;>
    dsimp [thirdDerivativeBarrier] <;> ring

theorem hasDerivAt_thirdDerivativeBarrier_space (τ x : ℝ) :
    HasDerivAt (fun y=>thirdDerivativeBarrier (τ,y)) (thirdDerivativeBarrierX (τ,x)) x := by
  have he:=((hasDerivAt_id x).pow 2).neg.exp
  convert (((hasDerivAt_id x).mul he).const_mul (2*Real.exp (-4)*Real.exp (-4*τ))) using 1 <;>
    dsimp [thirdDerivativeBarrier,thirdDerivativeBarrierX] <;> ring

theorem hasDerivAt_thirdDerivativeBarrierX_space (τ x : ℝ) :
    HasDerivAt (fun y=>thirdDerivativeBarrierX (τ,y)) (thirdDerivativeBarrierXX (τ,x)) x := by
  have he:=((hasDerivAt_id x).pow 2).neg.exp
  have hh:=((hasDerivAt_const x (1:ℝ)).sub (((hasDerivAt_id x).pow 2).const_mul 2)).mul he
  convert hh.const_mul (2*Real.exp (-4)*Real.exp (-4*τ)) using 1 <;>
    dsimp [thirdDerivativeBarrierX,thirdDerivativeBarrierXX] <;> ring

theorem thirdDerivativeBarrier_pos {τ x : ℝ} (hx : 0<x) : 0<thirdDerivativeBarrier (τ,x) := by
  unfold thirdDerivativeBarrier
  positivity

@[simp] theorem thirdDerivativeBarrier_zero (τ : ℝ) : thirdDerivativeBarrier (τ,0)=0 := by
  simp [thirdDerivativeBarrier]

theorem thirdDerivativeBarrier_generator_nonpos (b : ℝ×ℝ→ℝ) (τ x κ : ℝ)
    (hx : 0≤x) (hb : b (τ,x)∈Icc (0:ℝ) 1) (hκ : 0≤κ) :
    FRSB.backwardGenerator b thirdDerivativeBarrier (τ,x)-κ*thirdDerivativeBarrier (τ,x)≤0 := by
  have hfirst : deriv (fun y=>thirdDerivativeBarrier (τ,y))=
      fun y=>thirdDerivativeBarrierX (τ,y) :=
    funext fun y=>(hasDerivAt_thirdDerivativeBarrier_space τ y).deriv
  rw [FRSB.backwardGenerator,(hasDerivAt_thirdDerivativeBarrier_time τ x).deriv,
    hfirst,(hasDerivAt_thirdDerivativeBarrierX_space τ x).deriv]
  let c:=2*Real.exp (-4)*Real.exp (-4*τ)*Real.exp (-x^2)
  have hc : 0≤c := by dsimp [c];positivity
  have hpoly : -4*x-(4*x^3-6*x)/2-b (τ,x)*(1-2*x^2)-κ*x≤0 := by
    have hbx := mul_le_mul_of_nonneg_right hb.2 (sq_nonneg x)
    have hxx : x*(2*x^2-2*x+1)≥0 :=
      mul_nonneg hx (by nlinarith [sq_nonneg (x-(1/2:ℝ))])
    nlinarith [hb.1,mul_nonneg hκ hx]
  convert mul_nonpos_of_nonneg_of_nonpos hc hpoly using 1 <;>
    dsimp [thirdDerivativeBarrier,thirdDerivativeBarrierX,thirdDerivativeBarrierXX,c] <;> ring

theorem thirdDerivativeBarrier_terminal_le {x : ℝ} (hx : 0≤x) :
    thirdDerivativeBarrier (0,x)≤2*Real.tanh x*Paper.sech x^2 := by
  have ht : x*Paper.sech x^2≤Real.tanh x := by
    rcases eq_or_lt_of_le hx with rfl|hx
    · simp
    · exact (sub_pos.mp (Paper.tanh_sub_mul_sech_sq_pos hx)).le
  have he : Real.exp (-x)≤Paper.sech x := by
    have hcosh : Real.cosh x≤Real.exp x := by
      rw [Real.cosh_eq]
      have hh:=Real.exp_le_exp.mpr (show -x≤x by linarith)
      linarith
    apply (le_div_iff₀ (Real.cosh_pos x)).mpr
    calc
      _≤Real.exp (-x)*Real.exp x:=mul_le_mul_of_nonneg_left hcosh (Real.exp_pos _).le
      _=1 := by rw [←Real.exp_add];simp
  have hpow:=pow_le_pow_left₀ (Real.exp_pos (-x)).le he 4
  have heq : Real.exp (-4*x)=(Real.exp (-x))^4 := by
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  have hbar : Real.exp (-4-x^2)≤Real.exp (-4*x) :=
    Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (x-2)])
  calc
    _=2*x*Real.exp (-4-x^2) := by
      unfold thirdDerivativeBarrier
      simp only [Prod.fst,Prod.snd,mul_zero,Real.exp_zero,mul_one]
      rw [show -4-x^2=(-4:ℝ)+(-x^2) by ring,Real.exp_add]
      ring
    _≤2*x*Real.exp (-4*x) := mul_le_mul_of_nonneg_left hbar (by positivity)
    _≤2*x*Paper.sech x^4 := mul_le_mul_of_nonneg_left (by simpa only [heq] using hpow) (by positivity)
    _≤2*Real.tanh x*Paper.sech x^2 := by
      have hh:=mul_le_mul_of_nonneg_right ht (sq_nonneg (Paper.sech x))
      nlinarith


theorem thirdDerivativeBarrier_bounded (τ x : ℝ) (hτ : 0≤τ) :
    |thirdDerivativeBarrier (τ,x)|≤2*Real.exp (-4) := by
  have hx : |x|≤Real.exp (x^2) := by
    nlinarith [Real.add_one_le_exp (x^2),sq_abs x,sq_nonneg (|x|-(1/2:ℝ))]
  have hg : |x*Real.exp (-x^2)|≤1 := by
    rw [abs_mul,abs_of_pos (Real.exp_pos _)]
    calc
      _≤Real.exp (x^2)*Real.exp (-x^2):=mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le
      _=1:=by rw [←Real.exp_add];simp
  have ht : Real.exp (-4*τ)≤1 := Real.exp_le_one_iff.mpr (by linarith)
  have hp : 0≤2*Real.exp (-4)*Real.exp (-4*τ) := by positivity
  calc
    _=(2*Real.exp (-4)*Real.exp (-4*τ))*|x*Real.exp (-x^2)| := by
      rw [thirdDerivativeBarrier,show 2*Real.exp (-4)*Real.exp (-4*τ)*x*Real.exp (-x^2)=
        (2*Real.exp (-4)*Real.exp (-4*τ))*(x*Real.exp (-x^2)) by ring,abs_mul,abs_of_nonneg hp]
    _≤2*Real.exp (-4)*Real.exp (-4*τ):=by nlinarith
    _≤2*Real.exp (-4):=mul_le_of_le_one_right (by positivity) ht

theorem thirdDerivativeBarrier_classicalCell (a b : ℝ) (ha : 0≤a) :
    FRSB.IsBoundedClassicalCell a b thirdDerivativeBarrier := by
  refine ⟨contDiff_thirdDerivativeBarrier.continuous.continuousOn,
    ⟨2*Real.exp (-4),by positivity,fun τ hτ x=>thirdDerivativeBarrier_bounded τ x (ha.trans hτ.1)⟩,
    fun τ _ x=>(hasDerivAt_thirdDerivativeBarrier_time τ x).differentiableAt,
    fun τ _ x=>(hasDerivAt_thirdDerivativeBarrier_space τ x).differentiableAt,?_⟩
  intro τ _ x
  rw [show deriv (fun y=>thirdDerivativeBarrier (τ,y))=
    (fun y=>thirdDerivativeBarrierX (τ,y)) from
      funext fun y=>(hasDerivAt_thirdDerivativeBarrier_space τ y).deriv]
  exact (hasDerivAt_thirdDerivativeBarrierX_space τ x).differentiableAt

end QuantitativeFollowup
