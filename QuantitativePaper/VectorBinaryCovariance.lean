module
public import QuantitativePaper.VectorBackwardLinear

@[expose] public section

/-! Sharp conditional covariance domination for an actual binary terminal
spin. The finite normalized Gaussian recursion retains this bound; no
conditional covariance premise is supplied. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1400000

theorem vectorConditionalMean_mono {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b d e : Configuration n → ℝ)
    (hde : ∀σ,d σ≤e σ) (j : ℕ) (y : ℝ) (x : Field n) :
    vectorConditionalMean s β t p b d j y x≤vectorConditionalMean s β t p b e j y x := by
  let R:=∑σ:Configuration n,|d σ|
  let S:=∑σ:Configuration n,|e σ|
  have hd (σ:Configuration n) : |d σ|≤R:=
    Finset.single_le_sum (fun τ _=>abs_nonneg (d τ)) (Finset.mem_univ σ)
  have he (σ:Configuration n) : |e σ|≤S:=
    Finset.single_le_sum (fun τ _=>abs_nonneg (e τ)) (Finset.mem_univ σ)
  induction j generalizing x with
  | zero =>
    unfold vectorConditionalMean terminalMean
    exact Finset.sum_le_sum fun σ _=>
      mul_le_mul_of_nonneg_left (hde σ) (terminalWeight_pos _ σ).le
  | succ j ih =>
    exact vectorStepResponse_mono _ _ _ _ (vectorPerturbedRecursion_lipschitz s β t p b j y)
      ((measurable_vectorConditionalMean s β t p b d j).comp (measurable_const.prodMk measurable_id))
      ((measurable_vectorConditionalMean s β t p b e j).comp (measurable_const.prodMk measurable_id))
      R S (fun z=>abs_vectorConditionalMean_le s β t p b d R hd j y z)
      (fun z=>abs_vectorConditionalMean_le s β t p b e S he j y z) ih _ _ x

theorem vectorConditionalMean_sub {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b d e : Configuration n → ℝ)
    (j : ℕ) (y : ℝ) (x : Field n) :
    vectorConditionalMean s β t p b (fun σ=>d σ-e σ) j y x=
      vectorConditionalMean s β t p b d j y x-vectorConditionalMean s β t p b e j y x := by
  have hh:=vectorConditionalMean_add s β t p b d (fun σ=>(-1:ℝ)*e σ) j y x
  rw [vectorConditionalMean_const_mul] at hh
  simpa only [neg_one_mul,sub_eq_add_neg] using hh

theorem abs_vectorConditionalMean_le_mean_abs {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b d : Configuration n → ℝ)
    (j : ℕ) (y : ℝ) (x : Field n) :
    |vectorConditionalMean s β t p b d j y x|≤
      vectorConditionalMean s β t p b (fun σ=>|d σ|) j y x := by
  apply abs_le.mpr
  constructor
  · have hh:=vectorConditionalMean_mono s β t p b (fun σ=>(-1:ℝ)*d σ)
      (fun σ=>|d σ|) (fun σ=>by simpa only [neg_one_mul] using neg_le_abs (d σ)) j y x
    rw [vectorConditionalMean_const_mul] at hh
    linarith
  · exact vectorConditionalMean_mono s β t p b d (fun σ=>|d σ|) (fun σ=>le_abs_self _) j y x

def vectorConditionalCrossCovariance {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (e b d : Configuration n → ℝ)
    (j : ℕ) (y : ℝ) (x : Field n) : ℝ :=
  vectorConditionalMean s β t p e (fun σ=>b σ*d σ) j y x-
    vectorConditionalMean s β t p e b j y x*vectorConditionalMean s β t p e d j y x

theorem measurable_vectorConditionalCrossCovariance {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (e b d : Configuration n → ℝ) (j : ℕ) :
    Measurable (fun w:ℝ×Field n=>vectorConditionalCrossCovariance s β t p e b d j w.1 w.2) :=
  (measurable_vectorConditionalMean s β t p e _ j).sub
    ((measurable_vectorConditionalMean s β t p e b j).mul
      (measurable_vectorConditionalMean s β t p e d j))

theorem vectorConditionalCrossCovariance_symm {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (e b d : Configuration n → ℝ) (j : ℕ) (y : ℝ) (x : Field n) :
    vectorConditionalCrossCovariance s β t p e b d j y x=
      vectorConditionalCrossCovariance s β t p e d b j y x := by
  unfold vectorConditionalCrossCovariance
  congr 1
  · congr 1
    funext σ
    ring
  · ring

theorem vectorConditionalCrossCovariance_binary_bound {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (e b d : Configuration n → ℝ)
    (hb : ∀σ,b σ=1 ∨ b σ= -1) (hd : ∀σ,|d σ|≤1)
    (j : ℕ) (y : ℝ) (x : Field n) :
    |vectorConditionalCrossCovariance s β t p e b d j y x|≤
      vectorConditionalCrossCovariance s β t p e b b j y x := by
  let M:=vectorConditionalMean s β t p e b j y x
  have hbnd (σ:Configuration n) : |b σ|≤1:=by rcases hb σ with h|h <;> rw [h] <;> norm_num
  have hM:=abs_le.mp (abs_vectorConditionalMean_le s β t p e b 1 hbnd j y x)
  have hpoint (σ:Configuration n) : |b σ-M|=1-M*b σ := by
    rcases hb σ with h|h
    · rw [h,abs_of_nonneg (by dsimp [M];linarith [hM.2])]
      ring
    · rw [h,abs_of_nonpos (by dsimp [M];linarith [hM.1])]
      ring
  have hcenter : vectorConditionalCrossCovariance s β t p e b d j y x=
      vectorConditionalMean s β t p e (fun σ=>(b σ-M)*d σ) j y x := by
    have hfun : (fun σ=>(b σ-M)*d σ)=(fun σ=>b σ*d σ-M*d σ):=by funext σ;ring
    rw [hfun,vectorConditionalMean_sub,vectorConditionalMean_const_mul]
    rfl
  have hcov : vectorConditionalCrossCovariance s β t p e b b j y x=1-M^2 := by
    have hfun : (fun σ=>b σ*b σ)=(fun _=> (1:ℝ)):=by
      funext σ
      rcases hb σ with h|h <;> rw [h] <;> norm_num
    unfold vectorConditionalCrossCovariance
    rw [hfun,vectorConditionalMean_const]
    dsimp [M]
    ring
  rw [hcenter,hcov]
  calc
    _≤vectorConditionalMean s β t p e (fun σ=>|(b σ-M)*d σ|) j y x :=
      abs_vectorConditionalMean_le_mean_abs s β t p e _ j y x
    _≤vectorConditionalMean s β t p e (fun σ=>1-M*b σ) j y x :=
      vectorConditionalMean_mono s β t p e _ _ (fun σ=>by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left (hd σ) (abs_nonneg _)).trans_eq (by rw [mul_one,hpoint])) j y x
    _=1-M^2 := by rw [vectorConditionalMean_sub,vectorConditionalMean_const,
      vectorConditionalMean_const_mul];dsimp [M];ring

theorem abs_vectorConditionalCrossCovariance_binary_le_one {n k : ℕ}
    (s : RSBScheme k) (β t : ℝ) (p : Couplings n × ℝ) (e b d : Configuration n → ℝ)
    (hb : ∀σ,b σ=1 ∨ b σ= -1) (hd : ∀σ,|d σ|≤1)
    (j : ℕ) (y : ℝ) (x : Field n) :
    |vectorConditionalCrossCovariance s β t p e b d j y x|≤1 := by
  apply (vectorConditionalCrossCovariance_binary_bound s β t p e b d hb hd j y x).trans
  have hh : (fun σ=>b σ*b σ)=fun _=> (1:ℝ):=by
    funext σ
    rcases hb σ with h|h <;> rw [h] <;> norm_num
  unfold vectorConditionalCrossCovariance
  rw [hh,vectorConditionalMean_const]
  nlinarith [sq_nonneg (vectorConditionalMean s β t p e b j y x)]

end QuantitativePaper
