module
public import QuantitativePaper.VectorProfilePosteriorExponentialMoment

@[expose] public section

/-! Every natural displacement moment of the genuine finite posterior
is uniformly bounded by an actual Wiener exponential moment. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 4000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def vectorProfilePosteriorPowerMomentBound (n : ℕ) (β t : ℝ) (r : ℕ) : ℝ :=
  (r.factorial:ℝ)*vectorProfilePosteriorExpMomentBound n β t 1

theorem vectorProfilePosteriorPowerMomentBound_nonneg (n : ℕ) (β t : ℝ) (r : ℕ) :
    0≤vectorProfilePosteriorPowerMomentBound n β t r :=
  mul_nonneg (Nat.cast_nonneg _) (vectorProfilePosteriorExpMomentBound_nonneg _ _ _ _)

private theorem nonnegative_pow_le_factorial_exp (u : ℝ) (hu : 0≤u) (r : ℕ) :
    u^r≤(r.factorial:ℝ)*Real.exp u := by
  have h:=Real.pow_div_factorial_le_exp u hu r
  have hf : 0<(r.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos r
  exact ((div_le_iff₀ hf).mp h).trans_eq (mul_comm _ _)

theorem vectorClampedGridPosterior_fieldEnvelope_pow_moment (μ : Paper.ParisiMeasure)
    (j : ℕ) (β t : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap)
    (p : Couplings n×ℝ) (x : Field n) (r : ℕ) :
    Integrable (fun z=>(vectorProfilePosteriorFieldEnvelope
      (vectorClampedScheme (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q q.property)
        β t p x (vectorDyadicIndex j+2) z.1)^r)
      (vectorTailGaussianPosterior
        (vectorClampedScheme (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q q.property)
          β t p x (vectorDyadicIndex j+3)) ∧
    (∫z,(vectorProfilePosteriorFieldEnvelope
      (vectorClampedScheme (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q q.property)
        β t p x (vectorDyadicIndex j+2) z.1)^r
      ∂vectorTailGaussianPosterior
        (vectorClampedScheme (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q q.property)
          β t p x (vectorDyadicIndex j+3))≤vectorProfilePosteriorPowerMomentBound n β t r := by
  let d:=vectorDyadicIndex j
  let s:=vectorClampedScheme (Paper.parisiGridRSBScheme μ d) q q.property
  let P:=vectorTailGaussianPosterior s β t p x (d+3)
  let E : ((Fin (d+3)→Field n)×Configuration n)→ℝ:=
    fun z=>vectorProfilePosteriorFieldEnvelope s β t p x (d+2) z.1
  have hE : Measurable E:=measurable_vectorClampedGridPosterior_fieldEnvelope μ j β t q p x
  have hn (z) : 0≤E z:=vectorProfilePosteriorFieldEnvelope_nonneg s β t p x _ z.1
  have hbd (z) : (E z)^r≤(r.factorial:ℝ)*Real.exp (E z):=
    nonnegative_pow_le_factorial_exp (E z) (hn z) r
  have he:=vectorClampedGridPosterior_fieldEnvelope_exp_moment μ j β t hβ ht q p x 1 zero_le_one
  simp only [one_mul] at he
  have hiExp : Integrable (fun z=>(r.factorial:ℝ)*Real.exp (E z)) P := he.1.const_mul _
  have hi : Integrable (fun z=>(E z)^r) P := by
    apply hiExp.mono' (hE.pow_const r).aestronglyMeasurable
    exact .of_forall fun z=>by
      rw [Real.norm_of_nonneg (pow_nonneg (hn z) r)]
      exact hbd z
  refine ⟨hi,?_⟩
  have hh:=integral_mono hi hiExp hbd
  rw [integral_const_mul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left he.2 (Nat.cast_nonneg _))

end QuantitativePaper
