module
public import FourPapersCommon.SmoothCellLocalization
public import Mathlib.Analysis.Normed.Operator.Prod

@[expose] public section

/-! Uniform field-slice cutoff jets with an unbounded fixed parameter.
No bounds on parameter derivatives of the original observable are needed. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 1800000
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] [HasContDiffBump (P×E)]

theorem norm_iteratedFDeriv_parameterSliceCutoff_le (j r : ℕ) (p : P) (x : E) :
    ‖iteratedFDeriv ℝ r (fun y : E=>expandingSmoothCutoff j (p,y)) x‖≤
      expandingCutoffJetConstant (E:=P×E) r := by
  let A : E→L[ℝ] P×E:=ContinuousLinearMap.inr ℝ P E
  let g : P×E→ℝ:=fun z=>expandingSmoothCutoff j (z+(p,0))
  have hg : ContDiff ℝ ∞ g:= (contDiff_expandingSmoothCutoff j).comp
    (contDiff_id.add contDiff_const)
  have hA : ‖A‖≤1:=by
    apply A.opNorm_le_bound (by norm_num)
    intro y
    simp [A,Prod.norm_def]
  have he : (fun y : E=>expandingSmoothCutoff j (p,y))=g∘A:=by
    funext y
    simp [g,A,Function.comp_def]
  rw [he,A.iteratedFDeriv_comp_right hg x (by simp)]
  have hh:=ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ r g (A x)) (fun _ : Fin r=>A)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hh
  have hn : ‖A‖^r≤1:=by simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg A) hA r
  apply hh.trans
  have hj : ‖iteratedFDeriv ℝ r g (A x)‖≤expandingCutoffJetConstant (E:=P×E) r:=by
    rw [show g=(fun z : P×E=>expandingSmoothCutoff j (z+(p,0))) from rfl,
      iteratedFDeriv_comp_add_right]
    exact norm_iteratedFDeriv_expandingSmoothCutoff_le_constant r j _
  exact (mul_le_mul hj hn (pow_nonneg (norm_nonneg A) _)
    (expandingCutoffJetConstant_pos r).le).trans (by simp only [mul_one,le_refl])

theorem norm_iteratedFDeriv_parameterSliceLocalized_le
    (j r : ℕ) (p : P) (f : E→ℝ) (hf : ContDiff ℝ ∞ f)
    (x : E) (B : ℝ) (hb : ∀i : ℕ,i≤r→‖iteratedFDeriv ℝ i f x‖≤B) :
    ‖iteratedFDeriv ℝ r (fun y=>expandingSmoothCutoff j (p,y)*f y) x‖≤
      localizedJetCoefficient (E:=P×E) r*B := by
  have hc : ContDiff ℝ ∞ (fun y : E=>expandingSmoothCutoff j (p,y)):=
    (contDiff_expandingSmoothCutoff j).comp (contDiff_const.prodMk contDiff_id)
  apply (norm_iteratedFDeriv_mul_le hc hf x (by simp)).trans
  rw [localizedJetCoefficient,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_parameterSliceCutoff_le j i p x)
      (Nat.cast_nonneg _)
  · exact hb (r-i) (Nat.sub_le _ _)
  · exact norm_nonneg _
  · exact mul_nonneg (Nat.cast_nonneg _) (expandingCutoffJetConstant_pos i).le

theorem norm_iteratedFDeriv_cellLocalized_slice_le
    (ρ : ℝ→ℝ) (j r : ℕ) (f : ℝ×(P×E)→ℝ)
    (q : ℝ) (p : P) (x : E) (hf : ContDiff ℝ ∞ (fun y=>f (q,(p,y))))
    (hρ : ‖ρ q‖≤1) (B : ℝ)
    (hb : ∀i : ℕ,i≤r→‖iteratedFDeriv ℝ i (fun y=>f (q,(p,y))) x‖≤B) :
    ‖iteratedFDeriv ℝ r (fun y=>cellLocalizedFunction ρ j f (q,(p,y))) x‖≤
      localizedJetCoefficient (E:=P×E) r*B := by
  let g : E→ℝ:=fun y=>expandingSmoothCutoff j (p,y)*f (q,(p,y))
  have hg : ContDiff ℝ ∞ g:=
    ((contDiff_expandingSmoothCutoff j).comp (contDiff_const.prodMk contDiff_id)).mul hf
  have he : (fun y=>cellLocalizedFunction ρ j f (q,(p,y)))=ρ q • g:=by
    funext y
    simp only [cellLocalizedFunction,Pi.smul_apply,smul_eq_mul,g]
    ring
  rw [he,iteratedFDeriv_const_smul_apply (hg.of_le (by simp)).contDiffAt,norm_smul]
  have hbound:=norm_iteratedFDeriv_parameterSliceLocalized_le j r p _ hf x B hb
  calc
    _ ≤ 1*‖iteratedFDeriv ℝ r g x‖:=mul_le_mul_of_nonneg_right hρ (norm_nonneg _)
    _ ≤ _:=by simpa only [one_mul,g] using hbound

theorem hasDerivAt_cellLocalizedFunction_time
    (ρ : ℝ→ℝ) (j : ℕ) (f : ℝ×(P×E)→ℝ) (q : ℝ) (z : P×E) (v : ℝ)
    (hρ : ρ=ᶠ[𝓝 q] (fun _=>1))
    (hf : HasDerivAt (fun r=>f (r,z)) v q) :
    HasDerivAt (fun r=>cellLocalizedFunction ρ j f (r,z))
      (expandingSmoothCutoff j z*v) q := by
  apply (hf.const_mul (expandingSmoothCutoff j z)).congr_of_eventuallyEq
  filter_upwards [hρ] with r hr
  simp only [cellLocalizedFunction,hr,one_mul]

end FourPapersCommon
