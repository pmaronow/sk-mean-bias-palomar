module
public import QuantitativePaper.VectorFiniteHessianStrict

@[expose] public section

/-! A normalized Gaussian step preserves a genuine exponential lower
bound. Constants are explicit Gaussian exponential integrals; zero masses
and zero variances are included. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace QuantitativePaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorGaussianNormLaplace (n : ℕ) (a : ℝ) : ℝ :=
  ∫ z : Field n,Real.exp (a*‖z‖) ∂fieldGaussian n

theorem vectorGaussianNormLaplace_pos (n : ℕ) (a : ℝ) :
    0<vectorGaussianNormLaplace n a := by
  apply (integral_pos_iff_support_of_nonneg (fun _=>(Real.exp_pos _).le)
    (SYK.integrable_exp_mul_norm (ι := Fin n) a)).mpr
  have hs : Function.support (fun z : Field n=>Real.exp (a*‖z‖))=univ := by
    ext z;simp [Function.mem_support,Real.exp_ne_zero]
  rw [hs,measure_univ]
  exact zero_lt_one

theorem abs_fieldShift_sub_lipschitz (f : Field n→ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) (c : ℝ) (x z : Field n) :
    |f (fieldShift c x z)-f x|≤(L : ℝ)*Real.sqrt c*‖z‖ := by
  have h:=hf.dist_le_mul (fieldShift c x z) x
  simpa only [Real.dist_eq,dist_eq_norm,Real.norm_eq_abs,fieldShift,add_sub_cancel_left,norm_smul,
    Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_assoc] using h

theorem vectorStepPartition_norm_upper (f : Field n→ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) (c m : ℝ) (x : Field n) :
    vectorStepPartition c m f x ≤
      Real.exp (m*f x)*vectorGaussianNormLaplace n (|m| *(L : ℝ)*Real.sqrt c) := by
  rw [vectorStepPartition,vectorGaussianNormLaplace,←integral_const_mul]
  apply integral_mono (integrable_exp_vectorStep f L hf c m x)
    ((SYK.integrable_exp_mul_norm (ι := Fin n) (|m| *(L : ℝ)*Real.sqrt c)).const_mul _)
  intro z
  dsimp only
  rw [←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hd:=mul_le_mul_of_nonneg_left (abs_fieldShift_sub_lipschitz f L hf c x z) (abs_nonneg m)
  have hh:=le_abs_self (m*(f (fieldShift c x z)-f x))
  rw [abs_mul] at hh
  nlinarith only [hd,hh]

theorem vectorStepWeight_norm_lower (f : Field n→ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) (c m : ℝ) (x z : Field n) :
    Real.exp (-(|m| *(L : ℝ)*Real.sqrt c)*‖z‖)/
      vectorGaussianNormLaplace n (|m| *(L : ℝ)*Real.sqrt c) ≤vectorStepWeight c m f x z := by
  let A:=|m| *(L : ℝ)*Real.sqrt c
  have hG:=vectorGaussianNormLaplace_pos n A
  unfold vectorStepWeight
  apply (le_div_iff₀ (vectorStepPartition_pos f L hf c m x)).mpr
  calc
    _ ≤ (Real.exp (-A*‖z‖)/vectorGaussianNormLaplace n A)*
        (Real.exp (m*f x)*vectorGaussianNormLaplace n A) :=
      mul_le_mul_of_nonneg_left (vectorStepPartition_norm_upper f L hf c m x) (by positivity)
    _ = Real.exp (m*f x)*Real.exp (-A*‖z‖) := by field_simp <;> ring
    _ = Real.exp (m*f x-A*‖z‖) := by rw [←Real.exp_add];congr 1;ring
    _ ≤ Real.exp (m*f (fieldShift c x z)) := by
      apply Real.exp_le_exp.mpr
      have hd:=mul_le_mul_of_nonneg_left (abs_fieldShift_sub_lipschitz f L hf c x z) (abs_nonneg m)
      have hh:=neg_le_abs (m*(f (fieldShift c x z)-f x))
      rw [abs_mul] at hh
      dsimp only [A]
      nlinarith only [hd,hh]

def vectorGaussianLowerCoefficient (n : ℕ) (c m : ℝ) (L : ℝ≥0) (K : ℝ) : ℝ :=
  vectorGaussianNormLaplace n (-((|m| *(L : ℝ)+K)*Real.sqrt c))/
    vectorGaussianNormLaplace n (|m| *(L : ℝ)*Real.sqrt c)

theorem vectorGaussianLowerCoefficient_pos (n : ℕ) (c m : ℝ) (L : ℝ≥0) (K : ℝ) :
    0<vectorGaussianLowerCoefficient n c m L K :=
  div_pos (vectorGaussianNormLaplace_pos _ _) (vectorGaussianNormLaplace_pos _ _)

theorem vectorStepResponse_exponential_lower (f v : Field n→ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) (hv : Measurable v) (R : ℝ) (hb : ∀x,|v x|≤R)
    (d K : ℝ) (hd : 0≤d) (hK : 0≤K) (hlower : ∀x,d*Real.exp (-K*‖x‖)≤v x)
    (c m : ℝ) (x : Field n) :
    d*Real.exp (-K*‖x‖)*vectorGaussianLowerCoefficient n c m L K ≤
      vectorStepResponse c m f v x := by
  let A:=|m| *(L : ℝ)*Real.sqrt c
  let G:=vectorGaussianNormLaplace n A
  have hG:0<G:=vectorGaussianNormLaplace_pos _ _
  let D:=d*Real.exp (-K*‖x‖)/G
  have hInt : Integrable (fun z : Field n=>D*Real.exp (-(A+K*Real.sqrt c)*‖z‖)) (fieldGaussian n):=
    (SYK.integrable_exp_mul_norm (ι := Fin n) (-(A+K*Real.sqrt c))).const_mul D
  have hcmp (z : Field n) : D*Real.exp (-(A+K*Real.sqrt c)*‖z‖) ≤
      vectorStepWeight c m f x z*v (fieldShift c x z) := by
    have hn : ‖fieldShift c x z‖≤‖x‖+Real.sqrt c*‖z‖ := by
      simpa only [fieldShift,norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _)] using norm_add_le x (Real.sqrt c • z)
    have hvLower : d*Real.exp (-K*(‖x‖+Real.sqrt c*‖z‖))≤v (fieldShift c x z) := by
      apply LE.le.trans _ (hlower _)
      apply mul_le_mul_of_nonneg_left _ hd
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_le_mul_of_nonneg_left hn hK]
    calc
      _ = (Real.exp (-A*‖z‖)/G)*(d*Real.exp (-K*(‖x‖+Real.sqrt c*‖z‖))) := by
        dsimp [D]
        rw [show -(A+K*Real.sqrt c)*‖z‖=(-A*‖z‖)+(-K*Real.sqrt c*‖z‖) by ring,
          show -K*(‖x‖+Real.sqrt c*‖z‖)=(-K*‖x‖)+(-K*Real.sqrt c*‖z‖) by ring]
        simp only [Real.exp_add]
        ring
      _ ≤ vectorStepWeight c m f x z*v (fieldShift c x z) :=
        mul_le_mul (vectorStepWeight_norm_lower f L hf c m x z) hvLower
          (mul_nonneg hd (Real.exp_pos _).le) (vectorStepWeight_pos f L hf c m x z).le
  have h:=integral_mono hInt (integrable_vectorStepResponse_input f v L hf hv R hb c m x) hcmp
  rw [integral_const_mul] at h
  unfold vectorStepResponse
  convert h using 1
  change d*Real.exp (-K*‖x‖)*(vectorGaussianNormLaplace n
    (-((|m| *(L : ℝ)+K)*Real.sqrt c))/vectorGaussianNormLaplace n (|m| *(L : ℝ)*Real.sqrt c))=
    (d*Real.exp (-K*‖x‖)/vectorGaussianNormLaplace n (|m| *(L : ℝ)*Real.sqrt c))*
      vectorGaussianNormLaplace n (-(|m| *(L : ℝ)*Real.sqrt c+K*Real.sqrt c))
  rw [show -(|m| *(L : ℝ)*Real.sqrt c+K*Real.sqrt c)=
    -((|m| *(L : ℝ)+K)*Real.sqrt c) by ring]
  ring

end QuantitativePaper
