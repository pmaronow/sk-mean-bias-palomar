module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-! Exact factor-sixteen one-sided square-tail bounds from a conditional
comparison with a deterministic offset. -/
noncomputable section
open Set MeasureTheory
namespace FourPapersCommon
set_option maxHeartbeats 700000
variable {Ω : Type*} [MeasurableSpace Ω]

theorem upper_square_tail_bound (P : Measure Ω) (X Y : Ω→ℝ)
    (hX : Measurable X) (hXL : MemLp X 2 P) (hYL : MemLp Y 2 P)
    (d θ : ℝ) (hθ : 0<θ) (hd : d≤θ/2) (hcomp : X≤ᵐ[P]fun ω=>d+2*Y ω) :
    (∫ω,{ω | θ<X ω}.indicator (fun ω=>X ω^2) ω ∂P)≤16*(∫ω,Y ω^2 ∂P) := by
  have hset : MeasurableSet {ω | θ<X ω}:=measurableSet_lt measurable_const hX
  have hiX:=hXL.integrable_sq.indicator hset
  have h:=integral_mono_ae hiX (hYL.integrable_sq.const_mul 16) (show
      (fun ω=>{ω | θ<X ω}.indicator (fun ω=>X ω^2) ω)≤ᵐ[P]fun ω=>16*Y ω^2 from by
    filter_upwards [hcomp] with ω hω
    by_cases hx : θ<X ω
    · rw [indicator_of_mem (show ω∈{ω | θ<X ω} from hx)]
      have hXpos : 0<X ω:=hθ.trans hx
      have hY : X ω≤4*Y ω:=by linarith
      have hprod:=mul_nonneg (show 0≤4*Y ω-X ω by linarith) (show 0≤4*Y ω+X ω by linarith)
      nlinarith
    · rw [indicator_of_notMem (show ω∉{ω | θ<X ω} from hx)]
      positivity)
  simpa only [integral_const_mul] using h

theorem lower_square_tail_bound (P : Measure Ω) (X Y : Ω→ℝ)
    (hX : Measurable X) (hXL : MemLp X 2 P) (hYL : MemLp Y 2 P)
    (d θ : ℝ) (hθ : 0<θ) (hd : -θ/2≤d) (hcomp : (fun ω=>d+2*Y ω)≤ᵐ[P]X) :
    (∫ω,{ω | X ω< -θ}.indicator (fun ω=>X ω^2) ω ∂P)≤16*(∫ω,Y ω^2 ∂P) := by
  have hcomp' : (fun ω=>-X ω)≤ᵐ[P]fun ω=>-d+2*(-Y ω):=
    hcomp.mono fun ω hω=>by dsimp only at *;linarith
  have h:=upper_square_tail_bound P (fun ω=>-X ω) (fun ω=>-Y ω) hX.neg hXL.neg hYL.neg (-d) θ hθ
    (by linarith) hcomp'
  have hset : {ω | θ< -X ω}={ω | X ω< -θ} := by ext ω;simp only [mem_ofPred_eq];constructor <;> intro h <;> linarith
  simpa only [hset,neg_sq] using h

end FourPapersCommon
