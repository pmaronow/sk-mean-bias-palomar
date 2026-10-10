module
public import FourPapersCommon.NormalizedCGF
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

/-! Exact scaling and independent Gaussian completion of the actual
normalized logarithmic moment, including its removable value at zero. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace FourPapersCommon
set_option maxHeartbeats 300000

theorem normalizedCGF_const_mul {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω→ℝ)
    (hX : ∀a,Integrable (fun ω=>Real.exp (a*X ω)) P) (c a : ℝ) :
    normalizedCGF P (fun ω=>c*X ω) a=c*normalizedCGF P X (c*a) := by
  have h0 : 0∈interior (integrableExpSet X P) := by
    have he : integrableExpSet X P=univ := by ext b;simp [integrableExpSet,hX]
    simp [he]
  have h0c : 0∈interior (integrableExpSet (fun ω=>c*X ω) P) := by
    have he : integrableExpSet (fun ω=>c*X ω) P=univ := by
      ext b
      simp only [integrableExpSet,Set.mem_ofPred_eq,mem_univ,iff_true]
      convert hX (b*c) using 1
      funext ω
      congr 1
      ring
    simp [he]
  by_cases ha : a=0
  · subst a
    rw [mul_zero,normalizedCGF_zero P _ h0c,normalizedCGF_zero P X h0,integral_const_mul]
  by_cases hc : c=0
  · subst c
    rw [normalizedCGF_of_ne P _ ha]
    simp [cgf,mgf]
  rw [normalizedCGF_of_ne P _ ha,normalizedCGF_of_ne P X (mul_ne_zero hc ha)]
  have he : cgf (fun ω=>c*X ω) P a=cgf X P (c*a) := by
    unfold cgf mgf
    congr 2
    funext ω
    congr 1
    ring
  rw [he]
  field_simp

theorem normalizedCGF_gaussian_completion {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω→ℝ)
    (hX : ∀a,Integrable (fun ω=>Real.exp (a*X ω)) P) (c a : ℝ) :
    normalizedCGF (P.prod (gaussianReal 0 (1/2))) (fun z=>X z.1+c*z.2) a=
      normalizedCGF P X a+c^2*a/4 := by
  let Q:=P.prod (gaussianReal 0 (1/2))
  let Y:=fun z : Ω×ℝ=>X z.1+c*z.2
  have hY (b : ℝ) : Integrable (fun z=>Real.exp (b*Y z)) Q := by
    convert (hX b).mul_prod (integrable_exp_mul_gaussianReal (μ:=0) (v:=1/2) (b*c)) using 1
    funext z
    dsimp [Y]
    rw [mul_add,Real.exp_add]
    congr 1
    ring
  have h0 : 0∈interior (integrableExpSet X P) := by
    have he : integrableExpSet X P=univ := by ext b;simp [integrableExpSet,hX]
    simp [he]
  have h0Y : 0∈interior (integrableExpSet Y Q) := by
    have he : integrableExpSet Y Q=univ := by ext b;simp [integrableExpSet,hY]
    simp [he]
  by_cases ha : a=0
  · subst a
    rw [normalizedCGF_zero Q Y h0Y,normalizedCGF_zero P X h0]
    have hiX : Integrable X P := by
      simpa only [pow_one] using integrable_pow_of_integrable_exp_mul one_ne_zero (hX 1) (hX (-1)) 1
    have hiZ : Integrable (fun z : ℝ=>c*z) (gaussianReal 0 (1/2)) :=
      ((memLp_id_gaussianReal (μ:=0) (v:=1/2) 1).integrable le_rfl).const_mul c
    rw [integral_add (hiX.comp_fst _) (hiZ.comp_snd _),integral_fun_fst,integral_fun_snd,
      integral_const_mul,integral_id_gaussianReal]
    simp
  have hmgf : mgf Y Q a=mgf X P a*Real.exp (c^2*a^2/4) := by
    unfold mgf
    dsimp only [Y,Q]
    simp_rw [mul_add,Real.exp_add]
    rw [integral_prod_mul (fun ω=>Real.exp (a*X ω)) (fun z : ℝ=>Real.exp (a*(c*z)))]
    have hg:=congrFun (mgf_fun_id_gaussianReal (μ:=0) (v:=1/2)) (a*c)
    simp only [mgf,zero_mul,zero_add] at hg
    have hgauss : (∫z,Real.exp (a*(c*z)) ∂gaussianReal 0 (1/2))=Real.exp (c^2*a^2/4) := by
      convert hg using 1
      · congr 1;funext z;congr 1;ring
      · norm_num;ring
    rw [hgauss]
  rw [normalizedCGF_of_ne Q Y ha,normalizedCGF_of_ne P X ha]
  unfold cgf
  rw [hmgf,Real.log_mul (mgf_pos (hX a)).ne' (Real.exp_ne_zero _),Real.log_exp]
  field_simp <;> ring

end FourPapersCommon
