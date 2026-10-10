module
public import QuantitativeFollowup.FollowupCavityDecouplingTerminal
public import FourPapersCommon.SourceLogAverageProduct

@[expose] public section

/-! The actual scalar finite Parisi recursion, with the terminal spin
partition normalization retained. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets
open scoped BigOperators NNReal
namespace QuantitativeFollowup
variable {k : ℕ}
set_option maxHeartbeats 500000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

def cavityScalarFinite (s : RSBScheme k) (β : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  Real.log 2+parisiF s β j x

theorem cavityScalarFinite_zero (s : RSBScheme k) (β x : ℝ) :
    cavityScalarFinite s β 0 x=cavityScalarTerminal x := by
  have he : Real.exp x+Real.exp (-x)=2*Real.cosh x := by rw [Real.cosh_eq];ring
  unfold cavityScalarFinite parisiF cavityScalarTerminal
  rw [Fintype.sum_bool]
  simp only [Paper.spinSign, Bool.false_eq_true, ite_true, ite_false, mul_one, mul_neg_one]
  rw [he,Real.log_mul (by norm_num : (2:ℝ)≠0) (Real.cosh_pos x).ne']

theorem measurable_cavityScalarFinite (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    Measurable (cavityScalarFinite s β j) :=
  measurable_const.add (parisiF_measurable s β j)

theorem cavityScalarFinite_hasLinearGrowth (s : RSBScheme k) (β : ℝ) (j : ℕ) :
    HasLinearGrowth (cavityScalarFinite s β j) := by
  obtain ⟨C,D,hC,hD,hb⟩:=parisiF_hasLinearGrowth s β j
  refine ⟨|Real.log 2|+C,D,add_nonneg (abs_nonneg _) hC,hD,fun y=>?_⟩
  exact (abs_add_le _ _).trans (by linarith [hb y])

theorem integrable_cavityScalarFinite_shift (s : RSBScheme k) (β : ℝ) (j : ℕ) (x v : ℝ) :
    Integrable (fun z=>cavityScalarFinite s β j (x+Real.sqrt v*z)) (gaussianReal 0 1) :=
  integrable_of_hasLinearGrowth (cavityScalarFinite_hasLinearGrowth s β j)
    (measurable_cavityScalarFinite s β j) x v

theorem integrable_exp_cavityScalarFinite_shift (s : RSBScheme k) (β : ℝ) (j : ℕ) (x v a : ℝ) :
    Integrable (fun z=>Real.exp (a*cavityScalarFinite s β j (x+Real.sqrt v*z))) (gaussianReal 0 1) :=
  integrable_exp_mul_of_hasLinearGrowth (cavityScalarFinite_hasLinearGrowth s β j)
    (measurable_cavityScalarFinite s β j) a x v

theorem cavityScalarFinite_coleHopf (s : RSBScheme k) (β : ℝ) (j : ℕ) (x : ℝ) :
    OverlapPaper.sourceLogAverage (gaussianReal 0 1) (anisotropicSchemeMass s j)
      (fun z=>cavityScalarFinite s β j (x+Real.sqrt (β^2*(s.q (k+2-j)-s.q (k+1-j)))*z))=
      cavityScalarFinite s β (j+1) x := by
  have hh:=parisiStep_const_add (Real.log 2) (anisotropicSchemeMass s j)
    (β^2*(s.q (k+2-j)-s.q (k+1-j))) (parisiF_hasLinearGrowth s β j)
    (parisiF_measurable s β j) x
  simpa only [cavityScalarFinite,parisiF,anisotropicSchemeMass,OverlapPaper.sourceLogAverage,
    parisiStep,one_div,div_eq_mul_inv,mul_comm,one_mul] using hh

end QuantitativeFollowup
