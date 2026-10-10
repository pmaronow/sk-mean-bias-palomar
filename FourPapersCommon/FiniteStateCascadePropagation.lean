module
public import FourPapersCommon.FiniteStateCascadeHessianTelescoping

@[expose] public section

/-! Linear propagation through the actual normalized cascade kernels and
exact extension of the split-replica decomposition through outer layers. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators
namespace FourPapersCommon
open OverlapPaper SpinGlass.AT
set_option maxHeartbeats 1600000

section Linear
variable {A : Type*} [MeasurableSpace A]
theorem sourceKernelExpectation_const_mul (Q : ℕ → Kernel A A)
    (f : A → ℝ) (c : ℝ) (j : ℕ) (x : A) :
    sourceKernelExpectation Q j (fun y => c*f y) x =
      c*sourceKernelExpectation Q j f x := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    simp only [sourceKernelExpectation]
    simp_rw [ih]
    exact integral_const_mul _ _

theorem sourceKernelExpectation_add (Q : ℕ → Kernel A A)
    (hQ : ∀ j, IsMarkovKernel (Q j)) (f g : A → ℝ)
    (hf : Measurable f) (hg : Measurable g) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ x, |f x| ≤ C) (hbg : ∀ x, |g x| ≤ D) (j : ℕ) (x : A) :
    sourceKernelExpectation Q j (fun y => f y+g y) x =
      sourceKernelExpectation Q j f x + sourceKernelExpectation Q j g x := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    haveI := hQ j
    simp only [sourceKernelExpectation]
    simp_rw [ih]
    exact integral_add
      (source_bounded_integrable _ _ (sourceKernelExpectation_measurable Q f hf j) C
        (sourceKernelExpectation_abs_le Q hQ f hf C hC hb j))
      (source_bounded_integrable _ _ (sourceKernelExpectation_measurable Q g hg j) D
        (sourceKernelExpectation_abs_le Q hQ g hg D hD hbg j))

theorem sourceKernelExpectation_finsetSum {P : Type*} (s : Finset P)
    (Q : ℕ → Kernel A A) (hQ : ∀ j, IsMarkovKernel (Q j)) (f : P → A → ℝ)
    (hf : ∀ p ∈ s, Measurable (f p)) (C : P → ℝ)
    (hC : ∀ p ∈ s, 0 ≤ C p) (hb : ∀ p ∈ s, ∀ x, |f p x| ≤ C p)
    (j : ℕ) (x : A) :
    sourceKernelExpectation Q j (fun y => ∑ p ∈ s, f p y) x =
      ∑ p ∈ s, sourceKernelExpectation Q j (f p) x := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    haveI := hQ j
    simp only [sourceKernelExpectation]
    simp_rw [ih]
    exact integral_finsetSum _ (fun p hp =>
      source_bounded_integrable _ _ (sourceKernelExpectation_measurable Q _ (hf p hp) j) (C p)
        (sourceKernelExpectation_abs_le Q hQ _ (hf p hp) (C p) (hC p hp) (hb p hp) j))
end Linear

variable {S I : Type*} [Fintype S] [Fintype I] [Nonempty S]

theorem sourceKernelExpectation_cascadeFirst (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (p q : ℕ) (H K : FiniteStateField S) :
    sourceKernelExpectation
      (fun j => finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (p+j)) q
      (fun y => fderiv ℝ (finiteStateGaussianTerminalCascade V a L p) y K) H =
      fderiv ℝ (finiteStateGaussianTerminalCascade V a L (p+q)) H K := by
  induction q generalizing H with
  | zero => rfl
  | succ q ih =>
    simp only [sourceKernelExpectation]
    simp_rw [ih]
    rw [← fderiv_finiteStateGaussianTerminalCascade_succ_integral V a ha L]
    congr 2 <;> omega

theorem sourceKernelExpectation_cascadePair (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (p q k : ℕ) (H K M : FiniteStateField S) :
    sourceKernelExpectation
      (fun j => finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (p+q+j)) k
      (fun y => finiteStateCascadePairMoment V a L p q y K M) H =
      finiteStateCascadePairMoment V a L p (q+k) H K M := by
  induction k generalizing H with
  | zero => rfl
  | succ k ih =>
    simp only [sourceKernelExpectation]
    simp_rw [ih]
    rw [show q+(k+1) = (q+k)+1 by omega, finiteStateCascadePairMoment_succ]
    simp only [add_assoc]

variable [MeasurableSpace S] [MeasurableSingletonClass S]

theorem finiteStateCascadeHessian_propagated_pair_decomposition (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j q : ℕ) (H K M : FiniteStateField S) :
    sourceKernelExpectation
      (fun p => finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (j+p)) q
      (fun y => fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) y K M +
        a j * fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) y K *
          fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) y M) H =
      fderiv ℝ (finiteStateGaussianTerminalCascade V a L (j+q)) H (finiteStatePointwiseProduct K M) +
        (a 0-1)*finiteStateCascadePairMoment V a L 0 (j+q) H K M +
        ∑ p ∈ Finset.range j, (a (p+1)-a p)*
          finiteStateCascadePairMoment V a L (p+1) ((j+q)-(p+1)) H K M := by
  classical
  let Q := fun p => finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (j+p)
  have hQ : ∀ p, IsMarkovKernel (Q p) :=
    fun p => isMarkovKernel_finiteStateGaussianTerminalCascadeKernel V a ha L (j+p)
  let f := fun y => fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) y (finiteStatePointwiseProduct K M)
  let g := fun y => (a 0-1)*finiteStateCascadePairMoment V a L 0 j y K M
  let b := fun p y => (a (p+1)-a p)*finiteStateCascadePairMoment V a L (p+1) (j-(p+1)) y K M
  let D := ‖K‖*‖M‖
  have hD : 0 ≤ D := mul_nonneg (norm_nonneg K) (norm_nonneg M)
  have hd := (contDiff_one_finiteStateGaussianTerminalCascade V a ha L j).continuous_fderiv (by norm_num)
  have hfm : Measurable f := (hd.clm_apply continuous_const).measurable
  have hgm : Measurable g := (finiteStateCascadePairMoment_measurable V a ha L 0 j K M).const_mul _
  have hbm (p : ℕ) : Measurable (b p) :=
    (finiteStateCascadePairMoment_measurable V a ha L (p+1) (j-(p+1)) K M).const_mul _
  have hfb (y) : |f y| ≤ ‖finiteStatePointwiseProduct K M‖ :=
    finiteStateCascadeFirst_abs_le V a ha L j y _
  have hgb (y) : |g y| ≤ |a 0-1| *D := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (finiteStateCascadePairMoment_abs_le V a ha L 0 j y K M) (abs_nonneg _)
  have hbb (p y) : |b p y| ≤ |a (p+1)-a p| *D := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (finiteStateCascadePairMoment_abs_le V a ha L (p+1) (j-(p+1)) y K M) (abs_nonneg _)
  have hsmb : Measurable (fun y => ∑ p ∈ Finset.range j, b p y) :=
    Finset.measurable_sum _ (fun p _ => hbm p)
  have hsbb (y) : |∑ p ∈ Finset.range j, b p y| ≤ ∑ p ∈ Finset.range j, |a (p+1)-a p| *D :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => hbb p y)
  simp_rw [finiteStateCascadeHessian_pair_decomposition V a ha L j]
  change sourceKernelExpectation Q q (fun y => f y+g y+∑ p ∈ Finset.range j, b p y) H = _
  rw [sourceKernelExpectation_add Q hQ (fun y => f y+g y) _ (hfm.add hgm) hsmb
      (‖finiteStatePointwiseProduct K M‖+|a 0-1| *D) (∑ p ∈ Finset.range j, |a (p+1)-a p| *D)
      (by positivity) (Finset.sum_nonneg (fun p _ => mul_nonneg (abs_nonneg _) hD))
      (fun y => (abs_add_le _ _).trans (add_le_add (hfb y) (hgb y))) hsbb,
    sourceKernelExpectation_add Q hQ f g hfm hgm _ _ (norm_nonneg _) (mul_nonneg (abs_nonneg _) hD) hfb hgb,
    sourceKernelExpectation_finsetSum _ Q hQ b (fun p _ => hbm p) _
      (fun p _ => mul_nonneg (abs_nonneg _) hD) (fun p _ y => hbb p y)]
  simp only [f, g, b]
  simp_rw [sourceKernelExpectation_const_mul]
  rw [sourceKernelExpectation_cascadeFirst V a ha L j q H]
  have hp0 := sourceKernelExpectation_cascadePair V a L 0 j q H K M
  simp only [zero_add] at hp0
  rw [hp0]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have hj : p+1+(j-(p+1)) = j := by have := Finset.mem_range.mp hp; omega
  have he := sourceKernelExpectation_cascadePair V a L (p+1) (j-(p+1)) q H K M
  rw [hj] at he
  rw [he]
  congr 2 <;> omega

end FourPapersCommon
