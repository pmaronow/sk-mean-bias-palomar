module
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-! A checked Chebyshev/secant argument for the genuine survival function
of a square-integrable real random variable. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace FourPapersCommon
set_option maxHeartbeats 1500000

 def realSurvival {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (T : Ω→ℝ) (x : ℝ) : ℝ :=
  P.real {ω | x≤T ω}

 theorem realSurvival_quartiles {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {T : Ω→ℝ} (hT : Measurable T) (hL : MemLp T 2 P)
    (D : ℝ) (hD : 0<D) (hV : variance T P=D^2) :
    3/4≤realSurvival P T ((∫ω,T ω ∂P)-2*D) ∧
      realSurvival P T ((∫ω,T ω ∂P)+2*D)≤1/4 := by
  let m:=∫ω,T ω ∂P
  have hb:=meas_ge_le_variance_div_sq hL (show 0<2*D by positivity)
  rw [hV] at hb
  have he : D^2/(2*D)^2=(1/4:ℝ) := by field_simp; ring
  rw [he] at hb
  have hbR : P.real {ω | 2*D≤|T ω-m|}≤1/4 := by
    have hh:=ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hb
    simpa only [measureReal_def,ENNReal.toReal_ofReal (by norm_num : 0≤(1/4:ℝ))] using hh
  have hu : realSurvival P T (m+2*D)≤1/4 := by
    apply (measureReal_mono ?_).trans hbR
    intro ω hω
    change m+2*D≤T ω at hω
    exact le_trans (by linarith [hω]) (le_abs_self (T ω-m))
  have hl : P.real {ω | T ω<m-2*D}≤1/4 := by
    apply (measureReal_mono ?_).trans hbR
    intro ω hω
    change T ω<m-2*D at hω
    exact le_trans (by linarith [hω]) (neg_le_abs (T ω-m))
  have hE : MeasurableSet {ω | T ω<m-2*D}:=measurableSet_lt hT measurable_const
  have hc:=measureReal_compl (μ:=P) hE
  have hs : {ω | T ω<m-2*D}ᶜ={ω | m-2*D≤T ω} := by ext ω; simp
  rw [hs,probReal_univ] at hc
  exact ⟨by change 3/4≤P.real {ω | m-2*D≤T ω}; linarith,hu⟩

 theorem logConcave_survival_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {T : Ω→ℝ} (hT : Measurable T) (hL : MemLp T 2 P)
    (hpos : ∀x,0<realSurvival P T x)
    (hconc : ConcaveOn ℝ univ (fun x=>Real.log (realSurvival P T x)))
    (D γ : ℝ) (hD : 0<D) (hV : variance T P=D^2) (hγ : γ≤D)
    (y : ℝ) (hy : 0≤y) :
    realSurvival P T ((∫ω,T ω ∂P)+y-γ)≤
      3*Real.exp (-(Real.log 3)*y/(4*D)) := by
  let m:=∫ω,T ω ∂P
  let c:=Real.log 3/(4*D)
  have hc : 0<c := by exact div_pos (Real.log_pos (by norm_num)) (by positivity)
  have hcD : c*(4*D)=Real.log 3 := by dsimp [c]; field_simp
  have hS1 (x : ℝ) : realSurvival P T x≤1 := by
    exact (measureReal_mono (subset_univ _)).trans_eq probReal_univ
  have hquart:=realSurvival_quartiles hT hL D hD hV
  have hfU : Real.log (realSurvival P T (m+2*D))≤Real.log (1/4:ℝ) :=
    Real.log_le_log (hpos _) hquart.2
  have hfL : Real.log (3/4:ℝ)≤Real.log (realSurvival P T (m-2*D)) :=
    Real.log_le_log (by norm_num) hquart.1
  have hlog : Real.log (1/4:ℝ)-Real.log (3/4:ℝ)= -Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num),Real.log_div (by norm_num) (by norm_num)]
    simp only [Real.log_one]
    ring
  have hfU0 : Real.log (realSurvival P T (m+2*D))≤0 := by
    exact hfU.trans (Real.log_nonpos (by norm_num) (by norm_num))
  have hfDiff : Real.log (realSurvival P T (m+2*D))-
      Real.log (realSurvival P T (m-2*D))≤-Real.log 3 := by linarith
  have hbound : realSurvival P T (m+y-γ)≤Real.exp (Real.log 3-c*y) := by
    by_cases hz : y-γ≤2*D
    · have he : 0≤Real.log 3-c*y := by nlinarith
      exact (hS1 _).trans (Real.one_le_exp_iff.mpr he)
    · have hz' : 2*D<y-γ := lt_of_not_ge hz
      have hh:=hconc.slope_anti_adjacent (x:=m-2*D) (y:=m+2*D) (z:=m+y-γ)
        (mem_univ _) (mem_univ _) (by linarith) (by linarith)
      have hden : (m+2*D)-(m-2*D)=4*D := by ring
      rw [hden] at hh
      have hratio : (Real.log (realSurvival P T (m+2*D))-
        Real.log (realSurvival P T (m-2*D)))/(4*D)≤-c := by
        apply (div_le_iff₀ (show 0<4*D by positivity)).mpr
        nlinarith
      have hh' := (div_le_iff₀ (show 0<(m+y-γ)-(m+2*D) by linarith)).mp (hh.trans hratio)
      have hfb : Real.log (realSurvival P T (m+y-γ))≤Real.log 3-c*y := by
        nlinarith
      rw [←Real.exp_log (hpos (m+y-γ))]
      exact Real.exp_le_exp.mpr hfb
  convert hbound using 1
  rw [Real.exp_sub,Real.exp_log (by norm_num : 0<(3:ℝ))]
  simp only [div_eq_mul_inv,←Real.exp_neg]
  congr 1
  dsimp [c]
  ring

end FourPapersCommon
