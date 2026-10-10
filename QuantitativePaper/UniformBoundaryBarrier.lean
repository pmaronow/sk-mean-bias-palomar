module
public import FourPapersCommon.CompactNegativeComparison
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-! The explicit exponential barrier and literal jets in source Lemma 5.1. -/
noncomputable section
open Set Filter
open scoped Topology
namespace QuantitativePaper
set_option maxHeartbeats 1200000

def uniformBoundaryAlpha (τ : ℝ) : ℝ:=32/τ
def uniformBoundaryPhase (τ ell : ℝ) (p : ℝ×ℝ) : ℝ:=p.2/ell-(τ-p.1)/τ
def uniformBoundaryBarrier (τ ell ε : ℝ) (p : ℝ×ℝ) : ℝ:=
  ε*Real.exp (-uniformBoundaryAlpha τ)*(Real.exp (uniformBoundaryAlpha τ*uniformBoundaryPhase τ ell p)-1)
def uniformBoundaryBarrierTime (τ ell ε : ℝ) (p : ℝ×ℝ) : ℝ:=
  ε*Real.exp (-uniformBoundaryAlpha τ)*Real.exp (uniformBoundaryAlpha τ*uniformBoundaryPhase τ ell p)*
    (uniformBoundaryAlpha τ/τ)
def uniformBoundaryBarrierFirst (τ ell ε : ℝ) (p : ℝ×ℝ) : ℝ:=
  ε*Real.exp (-uniformBoundaryAlpha τ)*Real.exp (uniformBoundaryAlpha τ*uniformBoundaryPhase τ ell p)*
    (uniformBoundaryAlpha τ/ell)
def uniformBoundaryBarrierSecond (τ ell ε : ℝ) (p : ℝ×ℝ) : ℝ:=
  ε*Real.exp (-uniformBoundaryAlpha τ)*Real.exp (uniformBoundaryAlpha τ*uniformBoundaryPhase τ ell p)*
    (uniformBoundaryAlpha τ/ell)^2

theorem continuous_uniformBoundaryBarrier (τ ell ε : ℝ) :
    Continuous (uniformBoundaryBarrier τ ell ε):=by
  unfold uniformBoundaryBarrier uniformBoundaryPhase
  fun_prop

theorem hasDerivAt_uniformBoundaryBarrier_time (τ ell ε r x : ℝ) :
    HasDerivAt (fun s=>uniformBoundaryBarrier τ ell ε (s,x))
      (uniformBoundaryBarrierTime τ ell ε (r,x)) r := by
  have hp : HasDerivAt (fun s=>x/ell-(τ-s)/τ) (1/τ) r:=by
    convert (hasDerivAt_const r (x/ell)).sub
      (((hasDerivAt_id r).const_sub τ).div_const τ) using 1
    · rfl
    · ring
  have hd:=(((hp.const_mul (uniformBoundaryAlpha τ)).exp).sub_const 1).const_mul
    (ε*Real.exp (-uniformBoundaryAlpha τ))
  convert hd using 1 <;> dsimp only [uniformBoundaryBarrier,uniformBoundaryBarrierTime,
    uniformBoundaryPhase] <;> ring

theorem hasDerivAt_uniformBoundaryBarrier_field (τ ell ε r x : ℝ) :
    HasDerivAt (fun y=>uniformBoundaryBarrier τ ell ε (r,y))
      (uniformBoundaryBarrierFirst τ ell ε (r,x)) x := by
  have hp : HasDerivAt (fun y=>y/ell-(τ-r)/τ) (1/ell) x:=
    ((hasDerivAt_id x).div_const ell).sub_const ((τ-r)/τ)
  have hd:=(((hp.const_mul (uniformBoundaryAlpha τ)).exp).sub_const 1).const_mul
    (ε*Real.exp (-uniformBoundaryAlpha τ))
  convert hd using 1 <;> dsimp only [uniformBoundaryBarrier,uniformBoundaryBarrierFirst,
    uniformBoundaryPhase] <;> ring

theorem hasDerivAt_uniformBoundaryBarrier_first (τ ell ε r x : ℝ) :
    HasDerivAt (fun y=>uniformBoundaryBarrierFirst τ ell ε (r,y))
      (uniformBoundaryBarrierSecond τ ell ε (r,x)) x := by
  have hp : HasDerivAt (fun y=>y/ell-(τ-r)/τ) (1/ell) x:=
    ((hasDerivAt_id x).div_const ell).sub_const ((τ-r)/τ)
  have hd:=(((hp.const_mul (uniformBoundaryAlpha τ)).exp).const_mul
    (ε*Real.exp (-uniformBoundaryAlpha τ))).mul_const (uniformBoundaryAlpha τ/ell)
  convert hd using 1 <;> dsimp only [uniformBoundaryBarrierFirst,uniformBoundaryBarrierSecond,
    uniformBoundaryPhase] <;> ring

theorem uniformBoundaryBarrier_deriv (τ ell ε r x : ℝ) :
    deriv (fun y=>uniformBoundaryBarrier τ ell ε (r,y)) x=
      uniformBoundaryBarrierFirst τ ell ε (r,x):=
  (hasDerivAt_uniformBoundaryBarrier_field τ ell ε r x).deriv

theorem uniformBoundaryBarrier_second_deriv (τ ell ε r x : ℝ) :
    deriv (deriv (fun y=>uniformBoundaryBarrier τ ell ε (r,y))) x=
      uniformBoundaryBarrierSecond τ ell ε (r,x):=by
  have he : deriv (fun y=>uniformBoundaryBarrier τ ell ε (r,y))=
      uniformBoundaryBarrierFirst τ ell ε ∘ (fun y=>(r,y)):=
    funext fun y=>uniformBoundaryBarrier_deriv τ ell ε r y
  rw [he]
  exact (hasDerivAt_uniformBoundaryBarrier_first τ ell ε r x).deriv

theorem uniformBoundaryBarrier_heat_subsolution (τ ell ε r x B : ℝ)
    (hτ : 0<τ) (hell : ell∈Ioc (0 : ℝ) 4) (hε : 0≤ε) (hB : 0≤B) :
    uniformBoundaryBarrierTime τ ell ε (r,x)-
      (1/2 : ℝ)*uniformBoundaryBarrierSecond τ ell ε (r,x)-
      B*uniformBoundaryBarrierFirst τ ell ε (r,x)≤0 := by
  have hα : 0<uniformBoundaryAlpha τ:=div_pos (by norm_num) hτ
  have hs : 2*ell^2≤32:=by
    nlinarith [mul_le_mul_of_nonneg_left hell.2 hell.1.le,
      mul_le_mul_of_nonneg_left hell.2 (by norm_num : (0 : ℝ)≤4)]
  have hh:=div_le_div_of_nonneg_left hα.le (mul_pos (by norm_num : (0 : ℝ)<2)
    (sq_pos_of_pos hell.1)) hs
  have he : uniformBoundaryAlpha τ/32=1/τ:=by unfold uniformBoundaryAlpha;ring
  rw [he] at hh
  have hcoef : 1/τ-uniformBoundaryAlpha τ/(2*ell^2)-B/ell≤0:=by
    linarith [div_nonneg hB hell.1.le]
  calc
    _=ε*Real.exp (-uniformBoundaryAlpha τ)*Real.exp
      (uniformBoundaryAlpha τ*uniformBoundaryPhase τ ell (r,x))*uniformBoundaryAlpha τ*
      (1/τ-uniformBoundaryAlpha τ/(2*ell^2)-B/ell):=by
        unfold uniformBoundaryBarrierTime uniformBoundaryBarrierFirst uniformBoundaryBarrierSecond
        field_simp [hτ.ne',hell.1.ne'] <;> ring
    _≤0:=mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (mul_nonneg (mul_nonneg hε (Real.exp_pos _).le) (Real.exp_pos _).le) hα.le) hcoef

theorem uniformBoundaryBarrier_lower (τ ell ε r x : ℝ)
    (hτ : 0<τ) (hell : ell∈Ioc (0 : ℝ) 4) (hε : 0≤ε) (hx : 0≤x) :
    (1/4 : ℝ)*uniformBoundaryAlpha τ*ε*Real.exp (-uniformBoundaryAlpha τ)*
      (x-4*(τ-r)/τ)≤uniformBoundaryBarrier τ ell ε (r,x) := by
  have hα : 0≤uniformBoundaryAlpha τ:=(div_pos (by norm_num : (0 : ℝ)<32) hτ).le
  have hp : x/4≤x/ell:=div_le_div_of_nonneg_left hx hell.1 hell.2
  have he:=Real.add_one_le_exp (uniformBoundaryAlpha τ*uniformBoundaryPhase τ ell (r,x))
  have hc : 0≤ε*Real.exp (-uniformBoundaryAlpha τ):=mul_nonneg hε (Real.exp_pos _).le
  calc
    _=ε*Real.exp (-uniformBoundaryAlpha τ)*uniformBoundaryAlpha τ*(x/4-(τ-r)/τ):=by ring
    _≤ε*Real.exp (-uniformBoundaryAlpha τ)*
        (uniformBoundaryAlpha τ*uniformBoundaryPhase τ ell (r,x)):=by
      unfold uniformBoundaryPhase
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (sub_le_sub_right hp ((τ-r)/τ)) hα) hc
    _≤uniformBoundaryBarrier τ ell ε (r,x):=by
      unfold uniformBoundaryBarrier
      exact mul_le_mul_of_nonneg_left (by linarith) hc

end QuantitativePaper
