module
public import QuantitativePaper.VectorBrownianPathEnvelope
public import QuantitativePaper.VectorFiniteExponentialLocalization

@[expose] public section

/-! A single genuine exponential envelope for the actual finite-profile
state at every time, including both overlap endpoints and arbitrary tilt. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace QuantitativePaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n k : ℕ}

def vectorFiniteStatePathEnvelope (β t : ℝ) (sample : VectorDisorderBrownianSample n) : ℝ :=
  ((1-t)*β^2)*Real.sqrt (n : ℝ)+
    Real.sqrt ((1-t)*β^2)*vectorBrownianPathEnvelope sample.2

theorem norm_vectorFiniteState_le_pathEnvelope (s : SpinGlass.Targets.RSBScheme k)
    (β t : ℝ) (ht : t≤1) (r : ℝ≥0) (hr : r≤1) (sample : VectorDisorderBrownianSample n) :
    ‖vectorFiniteState s β t ht r sample‖≤vectorFiniteStatePathEnvelope β t sample := by
  exact (norm_vectorFiniteState_le s β t ht r hr sample).trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (norm_vectorBrownian_le_pathEnvelope r hr sample.2)
      (Real.sqrt_nonneg _)))

theorem measurable_vectorFiniteStatePathEnvelope (n : ℕ) (β t : ℝ) :
    Measurable (vectorFiniteStatePathEnvelope (n:=n) β t) :=
  measurable_const.add ((measurable_vectorBrownianPathEnvelope n).comp measurable_snd |>.const_mul _)

theorem integrable_exp_vectorFiniteStatePathEnvelope (s : SpinGlass.Targets.RSBScheme k)
    (β t outer K : ℝ) :
    Integrable (fun sample : VectorDisorderBrownianSample n=>
      Real.exp (K*(‖sample.1‖+vectorFiniteStatePathEnvelope β t sample)))
      (vectorFiniteDisorderTilt s β t outer) := by
  let c:=((1-t)*β^2)*Real.sqrt (n : ℝ)
  let σ:=Real.sqrt ((1-t)*β^2)
  let W:=vectorOuterWeight (n:=n) s β t outer
  have hW : Measurable W:=measurable_vectorOuterWeight s β t outer
  have hWpos (p : Couplings n×ℝ) : 0≤W p:=
    div_nonneg (Real.exp_pos _).le (vectorOuterPartition_pos s β t outer).le
  have hi:=((integrable_exp_vectorOuterWeight_norm (n:=n) s β t outer K).mul_prod
    (integrable_exp_vectorBrownianPathEnvelope (n:=n) (K*σ))).const_mul (Real.exp (K*c))
  have he : (fun sample : VectorDisorderBrownianSample n=>
      W sample.1*Real.exp (K*(‖sample.1‖+vectorFiniteStatePathEnvelope β t sample)))=
      (fun sample=>Real.exp (K*c)*(vectorOuterWeight s β t outer sample.1*
        Real.exp (K*‖sample.1‖)*Real.exp ((K*σ)*vectorBrownianPathEnvelope sample.2))):=by
    funext sample
    rw [show K*(‖sample.1‖+vectorFiniteStatePathEnvelope β t sample)=
      K*c+K*‖sample.1‖+(K*σ)*vectorBrownianPathEnvelope sample.2 by
        dsimp [vectorFiniteStatePathEnvelope,c,σ];ring]
    simp only [Real.exp_add]
    dsimp only [W]
    ring
  have hweighted : Integrable (fun sample : VectorDisorderBrownianSample n=>
      W sample.1*Real.exp (K*(‖sample.1‖+vectorFiniteStatePathEnvelope β t sample)))
      (vectorDisorderBrownianMeasure n):=by
    rw [he]
    exact hi
  rw [vectorFiniteDisorderTilt]
  apply (integrable_withDensity_iff_integrable_smul'
    (hW.comp measurable_fst).ennreal_ofReal (.of_forall fun _=>ENNReal.ofReal_lt_top)).mpr
  simpa only [Function.comp_apply,ENNReal.toReal_ofReal (hWpos _),smul_eq_mul] using hweighted

end QuantitativePaper
