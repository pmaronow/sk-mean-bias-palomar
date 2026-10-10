module
public import QuantitativeFollowup.GaussianShiftTailSemigroup
public import QuantitativeFollowup.AnisotropicTailContinuity

@[expose] public section

/-! Equal-mass blocks in a genuine Gaussian mesh compose to one Gaussian
step. The restart time can cut the first cell, and zero-length blocks remain
identity operators. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
set_option maxHeartbeats 600000
variable {S : Type} [Fintype S] {n : ℕ}

theorem gaussianShiftColeHopf_eq_finiteStateGaussianStep
    (A : Field n →L[ℝ]FiniteStateField S) (a : ℝ) (F : FiniteStateField S → ℝ) :
    gaussianShiftColeHopf A a F=finiteStateGaussianStep a A F := by
  funext H
  unfold gaussianShiftColeHopf gaussianShiftAverage gaussianShiftPartition
    finiteStateGaussianStep OverlapPaper.sourceLogAverage
  rw [fieldGaussian_eq_stdGaussian]

theorem gaussianShiftColeHopf_lipschitz_finite
    (A : Field n →L[ℝ]FiniteStateField S) (a : ℝ) (ha : 0 ≤ a)
    (F : FiniteStateField S → ℝ) (C : ℝ≥0) (hF : LipschitzWith C F) :
    LipschitzWith C (gaussianShiftColeHopf A a F) := by
  rw [gaussianShiftColeHopf_eq_finiteStateGaussianStep]
  exact finiteStateGaussianStep_lipschitz F hF a ha A

theorem gaussianUniformTailCascade_lipschitz (N : ℕ) (q : ℝ)
    (A : Field n →L[ℝ]FiniteStateField S) (a : ℝ → ℝ) (ha : ∀ x,0 ≤ a x)
    (F : FiniteStateField S → ℝ) (C : ℝ≥0) (hF : LipschitzWith C F) (j : ℕ) :
    LipschitzWith C (gaussianUniformTailCascade N q A a F j) := by
  induction j with
  | zero => exact hF
  | succ j ih => exact gaussianShiftColeHopf_lipschitz_finite _ _ (ha _) _ C ih

theorem gaussianUniformTailCascade_constant_block (N : ℕ) (q : ℝ)
    (A : Field n →L[ℝ]FiniteStateField S) (a : ℝ → ℝ) (ha : ∀ x,0 ≤ a x)
    (F : FiniteStateField S → ℝ) (C : ℝ≥0) (hF : LipschitzWith C F)
    (j l : ℕ) (hjl : j + l ≤ N) (m : ℝ) (hm : 0 ≤ m)
    (hb : ∀ i < l,a ((N-1-(j + i) : ℕ)/(N : ℝ))=m) :
    gaussianUniformTailCascade N q A a F (j + l)=
      gaussianShiftColeHopf
        (Real.sqrt (max q ((N-j : ℕ)/(N : ℝ))-
          max q ((N-(j + l) : ℕ)/(N : ℝ))) • A) m
        (gaussianUniformTailCascade N q A a F j) := by
  induction l with
  | zero =>
      simp only [Nat.add_zero,sub_self,Real.sqrt_zero,zero_smul]
      have hzero : (0:ℝ) • A=(0:Field n→L[ℝ]FiniteStateField S) := by ext z i;simp
      rw [hzero]
      exact (funext fun H=>gaussianShiftColeHopf_zero_input (n:=n)
        (gaussianUniformTailCascade N q A a F j) m H).symm
  | succ l ih =>
      have hjl' : j + l ≤ N := by omega
      rw [show j+(l + 1)=(j + l)+1 by omega,gaussianUniformTailCascade,
        hb l (by omega),ih hjl' (fun i hi=>hb i (by omega))]
      have hv : 0 ≤ max q ((N-(j + l) : ℕ)/(N : ℝ))-
          max q ((N-1-(j + l) : ℕ)/(N : ℝ)) := by
        apply sub_nonneg.mpr
        apply max_le_max_left
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast (show N-1-(j + l) ≤ N-(j + l) by omega)
      have hw : 0 ≤ max q ((N-j : ℕ)/(N : ℝ))-
          max q ((N-(j + l) : ℕ)/(N : ℝ)) := by
        apply sub_nonneg.mpr
        apply max_le_max_left
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast (show N-(j + l) ≤ N-j by omega)
      funext H
      rw [gaussianShiftColeHopf_semigroup _ C
        (gaussianUniformTailCascade_lipschitz N q A a ha F C hF j) A m hm _ _ hv hw]
      have he : (max q ((N-(j+l) : ℕ)/(N : ℝ))-
          max q ((N-1-(j+l) : ℕ)/(N : ℝ)))+
          (max q ((N-j : ℕ)/(N : ℝ))-max q ((N-(j+l) : ℕ)/(N : ℝ)))=
          max q ((N-j : ℕ)/(N : ℝ))-max q ((N-(j+(l+1)) : ℕ)/(N : ℝ)) := by
        rw [show N-1-(j+l)=N-(j+(l+1)) by omega]
        ring
      rw [he,show j+(l+1)=j+l+1 by omega]

end QuantitativeFollowup
