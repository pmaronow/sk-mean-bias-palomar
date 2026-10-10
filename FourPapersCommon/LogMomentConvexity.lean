module
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-! Logarithmic exponential integration preserves actual pointwise convex
mixture inequalities. The normalization argument proves the required
Hölder inequality directly from convexity of the exponential. -/
noncomputable section
open MeasureTheory Set
namespace FourPapersCommon
set_option maxHeartbeats 600000
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

theorem integral_exp_pos_of_integrable (f : Ω → ℝ)
    (hf : Integrable (fun x => Real.exp (f x)) P) :
    0 < ∫x,Real.exp (f x) ∂P := by
  apply (integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le) hf).mpr
  have he : Function.support (fun x => Real.exp (f x)) = univ := by
    ext x; simp [Function.mem_support,Real.exp_ne_zero]
  rw [he]; simp

theorem log_integral_exp_mixture_le (f g h : Ω → ℝ)
    (hf : Integrable (fun x => Real.exp (f x)) P)
    (hg : Integrable (fun x => Real.exp (g x)) P)
    (hh : Integrable (fun x => Real.exp (h x)) P)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1)
    (hle : ∀x,h x ≤ (1-lam)*f x+lam*g x) :
    Real.log (∫x,Real.exp (h x) ∂P) ≤
      (1-lam)*Real.log (∫x,Real.exp (f x) ∂P) +
        lam*Real.log (∫x,Real.exp (g x) ∂P) := by
  let F := ∫x,Real.exp (f x) ∂P
  let G := ∫x,Real.exp (g x) ∂P
  let H := ∫x,Real.exp (h x) ∂P
  let K := (1-lam)*Real.log F+lam*Real.log G
  have hF : 0 < F := integral_exp_pos_of_integrable P f hf
  have hG : 0 < G := integral_exp_pos_of_integrable P g hg
  have hH : 0 < H := integral_exp_pos_of_integrable P h hh
  have hi (v : Ω → ℝ) (hv : Integrable (fun x => Real.exp (v x)) P) (b : ℝ) :
      Integrable (fun x => Real.exp (v x-b)) P := by
    simpa only [Real.exp_sub] using hv.div_const (Real.exp b)
  have hn (v : Ω → ℝ) (hv : Integrable (fun x => Real.exp (v x)) P)
      (hp : 0 < ∫x,Real.exp (v x) ∂P) :
      (∫x,Real.exp (v x-Real.log (∫y,Real.exp (v y) ∂P)) ∂P) = 1 := by
    simp_rw [Real.exp_sub,Real.exp_log hp]
    rw [integral_div,div_self hp.ne']
  have hb := integral_mono (hi h hh K)
    (((hi f hf (Real.log F)).const_mul (1-lam)).add
      ((hi g hg (Real.log G)).const_mul lam)) (fun x => by
        have he := convexOn_exp.2 (mem_univ (f x-Real.log F))
          (mem_univ (g x-Real.log G)) (sub_nonneg.mpr hlam.2) hlam.1
          (by ring : (1-lam)+lam=1)
        have ht : h x-K ≤ (1-lam)*(f x-Real.log F)+lam*(g x-Real.log G) := by
          dsimp only [K]; linarith [hle x]
        exact (Real.exp_le_exp.mpr ht).trans he)
  simp only [Pi.add_apply] at hb
  rw [integral_add ((hi f hf (Real.log F)).const_mul (1-lam))
      ((hi g hg (Real.log G)).const_mul lam),integral_const_mul,integral_const_mul,
      hn f hf hF,hn g hg hG] at hb
  have he : (fun x => Real.exp (h x-K)) = fun x => Real.exp (-K)*Real.exp (h x) := by
    funext x; rw [← Real.exp_add]; congr 1; ring
  rw [he,integral_const_mul] at hb
  have hHK : H ≤ Real.exp K := by
    calc
      H = Real.exp K*(Real.exp (-K)*H) := by
        rw [← mul_assoc,← Real.exp_add]; simp
      _ ≤ Real.exp K*1 := mul_le_mul_of_nonneg_left (by simpa only [mul_one,sub_add_cancel] using hb)
        (Real.exp_pos _).le
      _ = _ := mul_one _
  have hl := Real.log_le_log hH hHK
  simpa only [Real.log_exp] using hl

end FourPapersCommon
