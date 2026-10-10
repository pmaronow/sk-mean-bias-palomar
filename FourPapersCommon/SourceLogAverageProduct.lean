module
public import FourPapersCommon.FiniteStateCascadeGrowth
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Exact product factorization of logarithmic Gaussian averages for two
possibly different coordinate spaces, including mass zero. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace FourPapersCommon
variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]

theorem sourceLogAverage_prod_add (P : Measure E) [IsProbabilityMeasure P]
    (Q : Measure F) [IsProbabilityMeasure Q] (a : ℝ) (f : E→ℝ) (g : F→ℝ)
    (hf : Integrable f P) (hg : Integrable g Q)
    (he : Integrable (fun x=>Real.exp (a*f x)) P)
    (he' : Integrable (fun x=>Real.exp (a*g x)) Q) :
    OverlapPaper.sourceLogAverage (P.prod Q) a (fun z=>f z.1+g z.2)=
      OverlapPaper.sourceLogAverage P a f+OverlapPaper.sourceLogAverage Q a g := by
  by_cases ha : a=0
  · simp only [OverlapPaper.sourceLogAverage,ha,ite_true]
    rw [integral_add (hf.comp_fst Q) (hg.comp_snd P),integral_fun_fst,integral_fun_snd]
    simp only [probReal_univ,one_smul]
  · have hi : (∫z : E×F,Real.exp (a*(f z.1+g z.2)) ∂P.prod Q)=
        (∫x,Real.exp (a*f x) ∂P)*(∫x,Real.exp (a*g x) ∂Q) := by
      simp only [mul_add,Real.exp_add]
      exact integral_prod_mul (fun x=>Real.exp (a*f x)) (fun x=>Real.exp (a*g x))
    simp only [OverlapPaper.sourceLogAverage,ha,ite_false,hi]
    rw [Real.log_mul (integral_exp_pos he).ne' (integral_exp_pos he').ne',add_div]

end FourPapersCommon
