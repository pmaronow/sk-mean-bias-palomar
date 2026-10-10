module
public import QuantitativePaper.VectorTiltedExponentialLocalization

@[expose] public section

/-! Actual finite-profile exponential localization. Disorder and field are
retained and tilted by the literal finite recursion, without identifying
that recursion with a separately constructed measure potential. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace QuantitativePaper
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem integrable_exp_vectorRecursion_add_norm (s : SpinGlass.Targets.RSBScheme k)
    (β t a K : ℝ) :
    Integrable (fun p : Couplings n×ℝ =>
      Real.exp (a*vectorRecursion s β t p (k+2) 0+K*‖p‖)) (completionLaw n) := by
  let C := |a| *vectorDisorderNormConstant n β t+|K|
  apply ((integrable_exp_completion_norm n C).const_mul
    (Real.exp (|a| *|vectorRecursion (n := n) s β t (0,0) (k+2) 0|))).mono'
      ((Real.measurable_exp.comp (((measurable_vectorRecursion s β t (k+2)).comp (measurable_id.prodMk measurable_const)).const_mul a |>.add
        (measurable_norm.const_mul K))).aestronglyMeasurable)
  filter_upwards [] with p
  dsimp only [Function.comp_apply,Pi.add_apply]
  rw [Real.norm_of_nonneg (Real.exp_pos _).le,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hd := (vectorRecursion_disorder_bound s β t p (k+2) (0 : Field n)).trans
    (vectorDisorderEnvelope_le_norm n β t p)
  have hu : |vectorRecursion s β t p (k+2) (0 : Field n)| ≤
      |vectorRecursion (n := n) s β t (0,0) (k+2) 0|+vectorDisorderNormConstant n β t*‖p‖ := by
    have hh := abs_add_le (vectorRecursion (n := n) s β t (0,0) (k+2) (0 : Field n))
      (vectorRecursion s β t p (k+2) 0-vectorRecursion (n := n) s β t (0,0) (k+2) 0)
    rw [add_sub_cancel] at hh
    linarith
  have ha := mul_le_mul_of_nonneg_left hu (abs_nonneg a)
  have he : a*vectorRecursion s β t p (k+2) (0 : Field n) ≤
      |a| *|vectorRecursion s β t p (k+2) 0| := by
    rw [←abs_mul]
    exact le_abs_self _
  have hk := mul_le_mul_of_nonneg_right (le_abs_self K) (norm_nonneg p)
  dsimp [C]
  nlinarith only [ha,he,hk]

theorem integrable_exp_vectorOuterWeight_norm (s : SpinGlass.Targets.RSBScheme k)
    (β t a K : ℝ) :
    Integrable (fun p : Couplings n×ℝ =>
      vectorOuterWeight s β t a p*Real.exp (K*‖p‖)) (completionLaw n) := by
  convert (integrable_exp_vectorRecursion_add_norm s β t a K).div_const
    (vectorOuterPartition (n := n) s β t a) using 1
  funext p
  simp only [vectorOuterWeight,Real.exp_add]
  ring


theorem norm_vectorFiniteState_le (s : SpinGlass.Targets.RSBScheme k) (β t : ℝ) (ht : t≤1)
    (r : ℝ≥0) (hr : r≤1) (sample : VectorDisorderBrownianSample n) :
    ‖vectorFiniteState s β t ht r sample‖ ≤
      ((1-t)*β^2)*Real.sqrt n+Real.sqrt ((1-t)*β^2)*‖disorderVectorBrownian r sample‖ := by
  have hh := norm_vectorAdditiveState_increment_le (vectorFiniteDriftData (n := n) s β t ht)
    (Real.sqrt ((1-t)*β^2)) 0 1 0 r bot_le sample
  simp only [vectorAdditiveState_zero,sub_zero,NNReal.coe_zero,
    abs_of_nonneg (Real.sqrt_nonneg _)] at hh
  have hbound : ((vectorFiniteDriftData (n := n) s β t ht).bound : ℝ)=
      ((1-t)*β^2)*Real.sqrt n := rfl
  rw [hbound] at hh
  have he : disorderVectorBrownianIncrement 0 r sample=disorderVectorBrownian r sample := by
    simp [disorderVectorBrownianIncrement,disorderVectorBrownian]
  rw [he] at hh
  change ‖vectorFiniteState s β t ht r sample‖ ≤ _ at hh
  have hc : 0 ≤ ((1-t)*β^2)*Real.sqrt n :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg β)) (Real.sqrt_nonneg _)
  exact hh.trans (add_le_add (mul_le_of_le_one_right hc
    (show (r : ℝ)≤1 from hr)) le_rfl)

theorem integrable_exp_vectorFiniteState_and_disorder (s : SpinGlass.Targets.RSBScheme k)
    (β t outer K : ℝ) (ht : t≤1) (r : ℝ≥0) (hr : r≤1) :
    Integrable (fun sample : VectorDisorderBrownianSample n =>
      Real.exp (K*(‖sample.1‖+‖vectorFiniteState s β t ht r sample‖)))
      (vectorFiniteDisorderTilt s β t outer) := by
  let c := ((1-t)*β^2)*Real.sqrt (n : ℝ)
  let σ := Real.sqrt ((1-t)*β^2)
  let W := vectorOuterWeight (n := n) s β t outer
  have hW : Measurable W:=measurable_vectorOuterWeight s β t outer
  have hWpos (p : Couplings n×ℝ) : 0 ≤ W p:=by
    exact div_nonneg (Real.exp_pos _).le (vectorOuterPartition_pos s β t outer).le
  have hs : Measurable (vectorFiniteState (n := n) s β t ht r):=
    (measurable_uncurry_vectorFiniteState s β t ht).of_uncurry_left
  have hmeas : Measurable (fun sample : VectorDisorderBrownianSample n =>
      Real.exp (K*(‖sample.1‖+‖vectorFiniteState s β t ht r sample‖))):=
    Real.measurable_exp.comp ((measurable_fst.norm.add hs.norm).const_mul K)
  have hi := ((integrable_exp_vectorOuterWeight_norm (n := n) s β t outer |K|).mul_prod
    (integrable_exp_vectorBrownian_norm (n := n) r (|K| *σ))).const_mul (Real.exp (|K| *c))
  have hweighted : Integrable (fun sample : VectorDisorderBrownianSample n =>
      W sample.1*Real.exp (K*(‖sample.1‖+‖vectorFiniteState s β t ht r sample‖)))
      (vectorDisorderBrownianMeasure n) := by
    apply hi.mono' (((hW.comp measurable_fst).mul hmeas).aestronglyMeasurable)
    filter_upwards [] with sample
    dsimp only [Pi.mul_apply,Function.comp_apply]
    rw [Real.norm_of_nonneg (mul_nonneg (hWpos _) (Real.exp_pos _).le)]
    have hstate := norm_vectorFiniteState_le s β t ht r hr sample
    change ‖vectorFiniteState s β t ht r sample‖ ≤ c+σ*‖vectorBrownian r sample.2‖ at hstate
    calc
      _ ≤ W sample.1*Real.exp (|K| *(‖sample.1‖+‖vectorFiniteState s β t ht r sample‖)) := by
        apply mul_le_mul_of_nonneg_left _ (hWpos _)
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right (le_abs_self K) (add_nonneg (norm_nonneg _) (norm_nonneg _))
      _ ≤ W sample.1*Real.exp (|K| *(‖sample.1‖+(c+σ*‖vectorBrownian r sample.2‖))) := by
        apply mul_le_mul_of_nonneg_left _ (hWpos _)
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hstate) (abs_nonneg K)
      _ = Real.exp (|K| *c)*(vectorOuterWeight s β t outer sample.1*
          Real.exp (|K| *‖sample.1‖)*Real.exp ((|K| *σ)*‖vectorBrownian r sample.2‖)) := by
        rw [show |K| *(‖sample.1‖+(c+σ*‖vectorBrownian r sample.2‖))=
          |K| *c+|K| *‖sample.1‖+(|K| *σ)*‖vectorBrownian r sample.2‖ by ring]
        simp only [Real.exp_add]
        dsimp only [W]
        ring
  rw [vectorFiniteDisorderTilt]
  apply (integrable_withDensity_iff_integrable_smul'
    (hW.comp measurable_fst).ennreal_ofReal (.of_forall fun _=>ENNReal.ofReal_lt_top)).mpr
  simpa only [Function.comp_apply,ENNReal.toReal_ofReal (hWpos _),smul_eq_mul] using hweighted

end QuantitativePaper
