module
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.LHopital
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! Smooth radial transforms of genuinely even smooth functions. The
boundary is treated from the physical half-line, rather than by invoking a
square-root derivative at zero. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace FourPapersCommon

def weightedJetIntegral (f : ℝ → ℝ) (k p : ℕ) (x : ℝ) : ℝ :=
  ∫ s in 0..1, s ^ p * iteratedDeriv k f (s * x)

private theorem continuous_weightedJet_integrand (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (k p : ℕ) (x : ℝ) :
    Continuous (fun s : ℝ => s ^ p * iteratedDeriv k f (s * x)) := by
  exact (continuous_id.pow p).mul
    ((hf.continuous_iteratedDeriv k (by simp)).comp (continuous_id.mul continuous_const))

private theorem hasDerivAt_weightedJetIntegral (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (k p : ℕ) (x : ℝ) :
    HasDerivAt (weightedJetIntegral f k p) (weightedJetIntegral f (k+1) (p+1) x) x := by
  let R := ‖x‖ + 1
  have hc : Continuous (iteratedDeriv (k+1) f) := hf.continuous_iteratedDeriv (k+1) (by simp)
  obtain ⟨K,hK⟩ := (isCompact_Icc : IsCompact (Icc (-R) R)).exists_bound_of_continuousOn hc.continuousOn
  have hK0 : 0 ≤ K := (norm_nonneg (iteratedDeriv (k+1) f 0)).trans
    (hK 0 (by dsimp only [R]; constructor <;> linarith [norm_nonneg x]))
  have hbound : ∀ s ∈ Set.uIoc (0:ℝ) 1, ∀ y ∈ Metric.ball x 1,
      ‖s^(p+1) * iteratedDeriv (k+1) f (s*y)‖ ≤ K := by
    intro s hs y hy
    rw [uIoc_of_le zero_le_one] at hs
    have hsabs : |s| ≤ 1 := by rw [abs_of_pos hs.1];exact hs.2
    have hyabs : ‖y‖ ≤ R := by
      have hyx : ‖y-x‖ < 1 := by simpa only [Metric.mem_ball,dist_eq_norm] using hy
      calc
        ‖y‖ = ‖x+(y-x)‖ := by congr 1;ring
        _ ≤ ‖x‖+‖y-x‖ := norm_add_le _ _
        _ ≤ R := by dsimp only [R];linarith
    have harg : s*y∈Icc (-R) R := by
      have hh : |s*y| ≤ R := by
        rw [abs_mul]
        calc
          |s| * |y| ≤ 1*R := mul_le_mul hsabs hyabs (abs_nonneg _) (by norm_num)
          _ = R := one_mul _
      exact abs_le.mp hh
    rw [norm_mul,norm_pow]
    have hp : ‖s‖^(p+1) ≤ 1 := pow_le_one₀ (norm_nonneg _) hsabs
    exact (mul_le_mul hp (hK _ harg) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hder : ∀ s y : ℝ, HasDerivAt
      (fun z => s^p * iteratedDeriv k f (s*z))
      (s^(p+1)*iteratedDeriv (k+1) f (s*y)) y := by
    intro s y
    have hh := (((hf.differentiable_iteratedDeriv k
      (by exact_mod_cast WithTop.coe_lt_top k)) (s*y)).hasDerivAt.comp y
      ((hasDerivAt_id y).const_mul s)).const_mul (s^p)
    convert hh using 1
    · rfl
    · rw [iteratedDeriv_succ,pow_succ]
      ring
  have hh := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=volume)
    (F:=fun y s=>s^p*iteratedDeriv k f (s*y))
    (F':=fun y s=>s^(p+1)*iteratedDeriv (k+1) f (s*y))
    (bound:=fun _=>K) (Metric.ball_mem_nhds x (by norm_num : (0:ℝ)<1))
    (Eventually.of_forall fun y=>(continuous_weightedJet_integrand f hf k p y).aestronglyMeasurable)
    ((continuous_weightedJet_integrand f hf k p x).intervalIntegrable 0 1)
    (continuous_weightedJet_integrand f hf (k+1) (p+1) x).aestronglyMeasurable
    (ae_of_all _ hbound) intervalIntegrable_const
    (ae_of_all _ fun s _ y _=>hder s y)
  exact hh.2

private theorem iteratedDeriv_weightedJetIntegral (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (k p j : ℕ) (x : ℝ) :
    iteratedDeriv j (weightedJetIntegral f k p) x =
      weightedJetIntegral f (k+j) (p+j) x := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv j (weightedJetIntegral f k p) =
        weightedJetIntegral f (k+j) (p+j) := funext ih
    rw [he]
    simpa only [Nat.add_assoc] using
      (hasDerivAt_weightedJetIntegral f hf (k+j) (p+j) x).deriv

private theorem contDiff_weightedJetIntegral (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (k p : ℕ) : ContDiff ℝ ∞ (weightedJetIntegral f k p) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro j _ x
  have he : iteratedDeriv j (weightedJetIntegral f k p) =
      weightedJetIntegral f (k+j) (p+j) := funext (iteratedDeriv_weightedJetIntegral f hf k p j)
  rw [he]
  exact (hasDerivAt_weightedJetIntegral f hf (k+j) (p+j) x).differentiableAt

/-- A smooth full-line extension of the radial differentiation operator
`f'(x)/(2*x)` for even `f`, defined by an actual compact integral. -/
def evenRadialDerivative (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1/2:ℝ) * weightedJetIntegral f 2 0 x

theorem evenRadialDerivative_eq_integral (f : ℝ → ℝ) (x : ℝ) :
    evenRadialDerivative f x=(1/2:ℝ)*∫ s in 0..1,deriv (deriv f) (s*x) := by
  simp only [evenRadialDerivative,weightedJetIntegral,pow_zero,one_mul,
    iteratedDeriv_succ,iteratedDeriv_zero]

/-- All full-line derivatives of the actual radial differentiation operator. -/
theorem iteratedDeriv_evenRadialDerivative (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (k : ℕ) (x : ℝ) :
    iteratedDeriv k (evenRadialDerivative f) x =
      (1/2:ℝ)*∫ s in 0..1,s^k*iteratedDeriv (k+2) f (s*x) := by
  unfold evenRadialDerivative
  rw [iteratedDeriv_const_mul_field,iteratedDeriv_weightedJetIntegral f hf 2 0 k x]
  simp only [weightedJetIntegral,Nat.zero_add,Nat.add_comm 2 k]

theorem contDiff_evenRadialDerivative (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (evenRadialDerivative f) :=
  contDiff_const.mul (contDiff_weightedJetIntegral f hf 2 0)

private theorem even_secondJet (f : ℝ → ℝ) (he : ∀ x, f (-x)=f x) (x : ℝ) :
    iteratedDeriv 2 f (-x)=iteratedDeriv 2 f x := by
  have hfun : (fun y => f (-y))=f := funext he
  have hh := iteratedDeriv_comp_neg 2 f x
  rw [hfun] at hh
  simpa using hh.symm

private theorem deriv_even_zero (f : ℝ → ℝ) (he : ∀ x, f (-x)=f x) :
    deriv f 0=0 := by
  have hfun : (fun y => f (-y))=f := funext he
  have hh := deriv_comp_neg (f:=f) (x:=0)
  rw [hfun] at hh
  simp only [neg_zero] at hh
  linarith

theorem even_evenRadialDerivative (f : ℝ → ℝ) (he : ∀ x, f (-x)=f x) (x : ℝ) :
    evenRadialDerivative f (-x)=evenRadialDerivative f x := by
  unfold evenRadialDerivative weightedJetIntegral
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [mul_neg,even_secondJet f he]

theorem evenRadialDerivative_zero (f : ℝ → ℝ) :
    evenRadialDerivative f 0=iteratedDeriv 2 f 0/2 := by
  simp [evenRadialDerivative,weightedJetIntegral]
  ring

/-- The integral extension is the usual radial differential operator
away from zero; the identity without division also holds at zero. -/
theorem evenRadialDerivative_mul (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (he : ∀ x, f (-x)=f x) (x : ℝ) :
    (2*x)*evenRadialDerivative f x=deriv f x := by
  have hder : ∀ s∈uIcc (0:ℝ) 1,HasDerivAt (fun q=>deriv f (q*x))
      (iteratedDeriv 2 f (s*x)*x) s := by
    intro s _
    have hh := ((hf.differentiable_iteratedDeriv 1
      (by exact_mod_cast WithTop.coe_lt_top 1)) (s*x)).hasDerivAt.comp s
      ((hasDerivAt_id s).mul_const x)
    convert hh using 1
    · funext q
      simp only [iteratedDeriv_succ,iteratedDeriv_zero,Function.comp_apply,id_eq]
    · simp only [iteratedDeriv_succ,iteratedDeriv_zero,one_mul]
  have hi : IntervalIntegrable (fun s=>iteratedDeriv 2 f (s*x)*x) volume 0 1 := by
    exact (((hf.continuous_iteratedDeriv 2 (by simp)).comp
      (continuous_id.mul continuous_const)).mul continuous_const).intervalIntegrable 0 1
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hi
  simp only [one_mul,zero_mul,deriv_even_zero f he,sub_zero] at hh
  rw [intervalIntegral.integral_mul_const] at hh
  unfold evenRadialDerivative weightedJetIntegral
  simp only [pow_zero,one_mul]
  calc
    _ = (∫ s in 0..1,iteratedDeriv 2 f (s*x))*x := by ring
    _ = _ := hh

theorem evenRadialDerivative_eq_quotient (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (he : ∀ x, f (-x)=f x) {x : ℝ} (hx:x≠0) :
    evenRadialDerivative f x=deriv f x/(2*x) := by
  apply (eq_div_iff (by positivity : (2*x:ℝ)≠0)).mpr
  simpa only [mul_comm] using evenRadialDerivative_mul f hf he x

/-- The physical half-line radial transform. -/
def evenRadialTransform (f : ℝ → ℝ) (r : ℝ) : ℝ := f (Real.sqrt r)

theorem hasDerivAt_evenRadialTransform_pos (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (he : ∀ x, f (-x)=f x) {r : ℝ} (hr:0<r) :
    HasDerivAt (evenRadialTransform f)
      (evenRadialTransform (evenRadialDerivative f) r) r := by
  have hs : Real.sqrt r≠0 := (Real.sqrt_pos.mpr hr).ne'
  have hh := ((hf.differentiable (by simp)) (Real.sqrt r)).hasDerivAt.comp r
    (Real.hasDerivAt_sqrt hr.ne')
  convert hh using 1
  · rfl
  · unfold evenRadialTransform
    rw [evenRadialDerivative_eq_quotient f hf he hs]
    ring

theorem continuous_evenRadialTransform (f : ℝ → ℝ) (hf : Continuous f) :
    Continuous (evenRadialTransform f) := hf.comp Real.continuous_sqrt

theorem hasDerivWithinAt_evenRadialTransform_zero (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (he : ∀ x, f (-x)=f x) :
    HasDerivWithinAt (evenRadialTransform f) (evenRadialDerivative f 0) (Ici 0) 0 := by
  have hder : ∀ᶠ r in 𝓝[>] (0:ℝ),HasDerivAt
      (fun r=>evenRadialTransform f r-evenRadialTransform f 0)
      (evenRadialTransform (evenRadialDerivative f) r) r := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hasDerivAt_evenRadialTransform_pos f hf he hr).sub_const _
  have hden : ∀ᶠ r in 𝓝[>] (0:ℝ),HasDerivAt (fun r:ℝ=>r) 1 r := Eventually.of_forall hasDerivAt_id
  have hnum : Tendsto (fun r=>evenRadialTransform f r-evenRadialTransform f 0)
      (𝓝[>] 0) (𝓝 0) := by
    have hh : Tendsto (evenRadialTransform f) (𝓝[>] 0) (𝓝 (evenRadialTransform f 0)) :=
      (continuous_evenRadialTransform f hf.continuous).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [sub_self] using hh.sub (tendsto_const_nhds (x:=evenRadialTransform f 0))
  have hdenlim : Tendsto (fun r:ℝ=>r) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hdlim : Tendsto (evenRadialTransform (evenRadialDerivative f))
      (𝓝[>] 0) (𝓝 (evenRadialDerivative f 0)) := by
    have hh : Tendsto (evenRadialTransform (evenRadialDerivative f))
        (𝓝[>] 0) (𝓝 (evenRadialTransform (evenRadialDerivative f) 0)) :=
      (continuous_evenRadialTransform (evenRadialDerivative f)
        (contDiff_evenRadialDerivative f hf).continuous).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa [evenRadialTransform] using hh
  have hh := HasDerivAt.lhopital_zero_nhdsGT hder hden
    (Eventually.of_forall (fun _=>one_ne_zero)) hnum hdenlim
    (by simpa only [div_one] using hdlim)
  rw [hasDerivWithinAt_iff_tendsto_slope,Ici_sdiff_left]
  change Tendsto (fun r=>slope (evenRadialTransform f) 0 r) _ _
  simpa [slope_def_field,evenRadialTransform,div_eq_inv_mul] using hh

theorem hasDerivWithinAt_evenRadialTransform (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (he : ∀ x, f (-x)=f x) {r : ℝ} (hr:0≤r) :
    HasDerivWithinAt (evenRadialTransform f)
      (evenRadialTransform (evenRadialDerivative f) r) (Ici 0) r := by
  rcases hr.eq_or_lt with hzero|hpos
  · subst r
    simpa [evenRadialTransform] using hasDerivWithinAt_evenRadialTransform_zero f hf he
  · exact (hasDerivAt_evenRadialTransform_pos f hf he hpos).hasDerivWithinAt

theorem derivWithin_evenRadialTransform (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (he : ∀ x, f (-x)=f x) {r : ℝ} (hr:0≤r) :
    derivWithin (evenRadialTransform f) (Ici 0) r=
      evenRadialTransform (evenRadialDerivative f) r :=
  (hasDerivWithinAt_evenRadialTransform f hf he hr).derivWithin (uniqueDiffOn_Ici 0 r hr)

theorem contDiffOn_evenRadialTransform (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (he : ∀ x, f (-x)=f x) : ContDiffOn ℝ ∞ (evenRadialTransform f) (Ici 0) := by
  rw [contDiffOn_infty]
  intro n
  induction n generalizing f with
  | zero => simpa using (continuous_evenRadialTransform f hf.continuous).continuousOn
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ici 0)]
    refine ⟨fun r hr=>(hasDerivWithinAt_evenRadialTransform f hf he hr).differentiableWithinAt,
      ?_,?_⟩
    · intro hn
      simp at hn
    · have hh := ih (evenRadialDerivative f) (contDiff_evenRadialDerivative f hf)
        (even_evenRadialDerivative f he)
      exact hh.congr fun r hr=>derivWithin_evenRadialTransform f hf he hr

theorem evenRadialDerivative_second_zero (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    iteratedDeriv 2 (evenRadialDerivative f) 0=iteratedDeriv 4 f 0/6 := by
  unfold evenRadialDerivative
  rw [iteratedDeriv_const_mul_field,
    iteratedDeriv_weightedJetIntegral f hf 2 0 2 0]
  norm_num [weightedJetIntegral,intervalIntegral.integral_mul_const,integral_pow]
  ring

/-- Continuous radial first jet on the closed physical half-line. -/
def radialFirstJet (f : ℝ → ℝ) : ℝ → ℝ :=
  evenRadialTransform (evenRadialDerivative f)

/-- Continuous radial second jet on the closed physical half-line. -/
def radialSecondJet (f : ℝ → ℝ) : ℝ → ℝ :=
  evenRadialTransform (evenRadialDerivative (evenRadialDerivative f))

theorem radialFirstJet_zero (f : ℝ → ℝ) :
    radialFirstJet f 0=iteratedDeriv 2 f 0/2 := by
  simpa [radialFirstJet,evenRadialTransform] using evenRadialDerivative_zero f

theorem radialSecondJet_zero (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    radialSecondJet f 0=iteratedDeriv 4 f 0/12 := by
  simp only [radialSecondJet,evenRadialTransform,Real.sqrt_zero,evenRadialDerivative_zero,
    evenRadialDerivative_second_zero f hf]
  ring

theorem continuous_radialFirstJet (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    Continuous (radialFirstJet f) :=
  continuous_evenRadialTransform _ (contDiff_evenRadialDerivative f hf).continuous

theorem continuous_radialSecondJet (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    Continuous (radialSecondJet f) :=
  continuous_evenRadialTransform _
    (contDiff_evenRadialDerivative _ (contDiff_evenRadialDerivative f hf)).continuous

theorem contDiffOn_radialFirstJet (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (he : ∀ x, f (-x)=f x) : ContDiffOn ℝ ∞ (radialFirstJet f) (Ici 0) :=
  contDiffOn_evenRadialTransform _ (contDiff_evenRadialDerivative f hf)
    (even_evenRadialDerivative f he)

theorem contDiffOn_radialSecondJet (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (he : ∀ x, f (-x)=f x) : ContDiffOn ℝ ∞ (radialSecondJet f) (Ici 0) :=
  contDiffOn_evenRadialTransform _
    (contDiff_evenRadialDerivative _ (contDiff_evenRadialDerivative f hf))
    (even_evenRadialDerivative _ (even_evenRadialDerivative f he))

theorem hasDerivWithinAt_radialFirstJet (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (he : ∀ x, f (-x)=f x) {r : ℝ} (hr:0≤r) :
    HasDerivWithinAt (radialFirstJet f) (radialSecondJet f r) (Ici 0) r :=
  hasDerivWithinAt_evenRadialTransform _ (contDiff_evenRadialDerivative f hf)
    (even_evenRadialDerivative f he) hr

theorem radialFirstJet_eq_derivWithin (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (he : ∀ x, f (-x)=f x) {r : ℝ} (hr:0≤r) :
    radialFirstJet f r=derivWithin (evenRadialTransform f) (Ici 0) r :=
  (derivWithin_evenRadialTransform f hf he hr).symm

theorem radialSecondJet_eq_derivWithin (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (he : ∀ x, f (-x)=f x) {r : ℝ} (hr:0≤r) :
    radialSecondJet f r=derivWithin (radialFirstJet f) (Ici 0) r :=
  ((hasDerivWithinAt_radialFirstJet f hf he hr).derivWithin
    (uniqueDiffOn_Ici 0 r hr)).symm

theorem hasDerivWithinAt_radial_first_zero (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (he : ∀ x, f (-x)=f x) :
    HasDerivWithinAt (evenRadialTransform f) (iteratedDeriv 2 f 0/2) (Ici 0) 0 := by
  simpa only [evenRadialDerivative_zero] using
    hasDerivWithinAt_evenRadialTransform_zero f hf he

theorem hasDerivWithinAt_radial_second_zero (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (he : ∀ x, f (-x)=f x) :
    HasDerivWithinAt (radialFirstJet f) (iteratedDeriv 4 f 0/12) (Ici 0) 0 := by
  simpa only [radialSecondJet_zero f hf] using
    hasDerivWithinAt_radialFirstJet f hf he (r:=0) le_rfl

theorem radialFirstJet_eq_quotient {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (he : ∀ x, f (-x)=f x) {r : ℝ} (hr:0<r) :
    radialFirstJet f r=deriv f (Real.sqrt r)/(2*Real.sqrt r) :=
  evenRadialDerivative_eq_quotient f hf he (Real.sqrt_pos.mpr hr).ne'

theorem hasDerivAt_radialFirstJet_pos (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (he : ∀ x, f (-x)=f x) {r : ℝ} (hr:0<r) :
    HasDerivAt (radialFirstJet f) (radialSecondJet f r) r :=
  hasDerivAt_evenRadialTransform_pos _ (contDiff_evenRadialDerivative f hf)
    (even_evenRadialDerivative f he) hr

end FourPapersCommon
