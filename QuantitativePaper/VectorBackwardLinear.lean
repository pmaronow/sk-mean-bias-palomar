module
public import QuantitativePaper.VectorConditionalLaw

@[expose] public section

/-! Genuine finite linearity of the constructed terminal-observable backward
means. Finite spin observables supply their own boundedness hypotheses. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000

theorem vectorConditionalMean_const {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b : Configuration n → ℝ) (c : ℝ)
    (j : ℕ) (y : ℝ) (x : Field n) :
    vectorConditionalMean s β t p b (fun _ => c) j y x=c := by
  induction j generalizing x with
  | zero => exact terminalMean_const _ c
  | succ j ih =>
    simp only [vectorConditionalMean]
    have he : vectorConditionalMean s β t p b (fun _ => c) j y=fun _ => c := funext ih
    rw [he]
    exact vectorStepResponse_const _ _ (vectorPerturbedRecursion_lipschitz s β t p b j y) _ _ c x

theorem vectorConditionalMean_add {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b d e : Configuration n → ℝ)
    (j : ℕ) (y : ℝ) (x : Field n) :
    vectorConditionalMean s β t p b (fun σ => d σ+e σ) j y x=
      vectorConditionalMean s β t p b d j y x+vectorConditionalMean s β t p b e j y x := by
  let R := ∑σ : Configuration n,|d σ|
  let S := ∑σ : Configuration n,|e σ|
  have hd (σ : Configuration n) : |d σ|≤R :=
    Finset.single_le_sum (fun τ _ => abs_nonneg (d τ)) (Finset.mem_univ σ)
  have he (σ : Configuration n) : |e σ|≤S :=
    Finset.single_le_sum (fun τ _ => abs_nonneg (e τ)) (Finset.mem_univ σ)
  induction j generalizing x with
  | zero => exact terminalMean_add _ d e
  | succ j ih =>
    simp only [vectorConditionalMean]
    have hh : vectorConditionalMean s β t p b (fun σ => d σ+e σ) j y=
        fun z => vectorConditionalMean s β t p b d j y z+vectorConditionalMean s β t p b e j y z := funext ih
    rw [hh]
    exact vectorStepResponse_add _ _ _ _ (vectorPerturbedRecursion_lipschitz s β t p b j y)
      ((measurable_vectorConditionalMean s β t p b d j).comp (measurable_const.prodMk measurable_id))
      ((measurable_vectorConditionalMean s β t p b e j).comp (measurable_const.prodMk measurable_id)) R S
      (fun z => abs_vectorConditionalMean_le s β t p b d R hd j y z)
      (fun z => abs_vectorConditionalMean_le s β t p b e S he j y z) _ _ x

theorem vectorConditionalMean_const_mul {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b d : Configuration n → ℝ) (c : ℝ)
    (j : ℕ) (y : ℝ) (x : Field n) :
    vectorConditionalMean s β t p b (fun σ => c*d σ) j y x=
      c*vectorConditionalMean s β t p b d j y x := by
  induction j generalizing x with
  | zero => exact terminalMean_const_mul _ d c
  | succ j ih =>
    simp only [vectorConditionalMean]
    have he : vectorConditionalMean s β t p b (fun σ => c*d σ) j y=
        fun z => c*vectorConditionalMean s β t p b d j y z := funext ih
    rw [he]
    exact vectorStepResponse_mul_const _ _ _ _ c x

theorem vectorConditionalMean_finset_sum {n k : ℕ} {ι : Type*} (S : Finset ι)
    (s : RSBScheme k) (β t : ℝ) (p : Couplings n × ℝ)
    (b : Configuration n → ℝ) (d : ι → Configuration n → ℝ) (j : ℕ) (y : ℝ) (x : Field n) :
    vectorConditionalMean s β t p b (fun σ => ∑l∈S,d l σ) j y x=
      ∑l∈S,vectorConditionalMean s β t p b (d l) j y x := by
  classical
  induction S using Finset.induction with
  | empty => simpa using vectorConditionalMean_const s β t p b 0 j y x
  | @insert l S hl ih =>
    simp only [Finset.sum_insert hl]
    rw [vectorConditionalMean_add,ih]

theorem vectorBackwardMean_const_mul {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (d : Configuration n → ℝ) (c : ℝ) (i : ℕ) (x : VectorState n) :
    vectorBackwardMean s β t (fun σ => c*d σ) i x=c*vectorBackwardMean s β t d i x :=
  vectorConditionalMean_const_mul s β t x.1 _ d c _ 0 x.2

theorem vectorBackwardMean_finset_sum {n k : ℕ} {ι : Type*} (S : Finset ι)
    (s : RSBScheme k) (β t : ℝ) (d : ι → Configuration n → ℝ) (i : ℕ) (x : VectorState n) :
    vectorBackwardMean s β t (fun σ => ∑l∈S,d l σ) i x=
      ∑l∈S,vectorBackwardMean s β t (d l) i x :=
  vectorConditionalMean_finset_sum S s β t x.1 _ d _ 0 x.2

theorem vectorBackwardMean_fieldDot {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (i : ℕ) (x : VectorState n) (w : Field n) :
    vectorBackwardMean s β t (fun σ => fieldDot w σ) i x=
      ∑l : Fin n,w l*vectorMagnetization s β t x.1 (k+2-i) x.2 l := by
  unfold fieldDot
  rw [vectorBackwardMean_finset_sum]
  simp_rw [vectorBackwardMean_const_mul,vectorBackwardMean_spin]

end QuantitativePaper
