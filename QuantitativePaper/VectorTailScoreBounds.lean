module
public import QuantitativePaper.VectorTailPosteriorExpectation
public import QuantitativePaper.VectorEnergyRegularity
public import QuantitativeFollowup.CanonicalJetBounds

@[expose] public section

/-! Dimension-only bounds on the genuine posterior translation score and
its second derivative. The finite Stieltjes coefficients have total mass one. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ContDiff BigOperators InnerProductSpace
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem norm_vectorRecursion_firstJet_le (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (j : ℕ) (x : Field n) :
    ‖iteratedFDeriv ℝ 1 (vectorRecursion s β t p j) x‖ ≤ Real.sqrt (n : ℝ) := by
  rw [norm_iteratedFDeriv_one]
  simpa only [Real.coe_toNNReal _ (Real.sqrt_nonneg _)] using
    norm_fderiv_le_of_lipschitz ℝ (x₀ := x) (vectorRecursion_lipschitz s β t p j)

theorem norm_vectorRecursion_secondJet_le (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (j : ℕ) (x : Field n) :
    ‖iteratedFDeriv ℝ 2 (vectorRecursion s β t p j) x‖ ≤ (n : ℝ) := by
  rw [←norm_iteratedFDeriv_gradient (vectorRecursion s β t p j) 1 x,
    norm_iteratedFDeriv_one,
    (hasFDerivAt_gradient_hessianOperator (vectorRecursion s β t p j)
      ((contDiff_vectorRecursion_field s β t p j).of_le (by simp)) x).fderiv]
  exact norm_vectorFieldHessian_le s β t p j x

theorem vectorTailHistoryPotential_eq_translate (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (j i : ℕ) (z : Fin j → Field n) :
    (fun x => vectorTailHistoryPotential s β t p x j i z)=
      fun x => vectorRecursion s β t p (j-i)
        (x+(vectorHistoryFrom s β t (k+2-j) p 0 j z (Fin.ofNat (j+1) i)).2) := by
  funext x
  unfold vectorTailHistoryPotential historyExtended
  rw [vectorHistoryFrom_field_eq_initial_add]

theorem vectorTerminalExponent_eq_affine (β t : ℝ) (p : Couplings n × ℝ)
    (w : Field n) (σ : Configuration n) :
    (fun x : Field n => vectorTerminalExponent n β t p (x+w) σ)=
      fun x => vectorTerminalExponent n β t p w σ+innerSL ℝ (spinVector σ) x := by
  funext x
  unfold vectorTerminalExponent
  rw [fieldDot_eq_inner,fieldDot_eq_inner,inner_add_left]
  simp only [innerSL_apply_apply]
  rw [real_inner_comm (spinVector σ) x]
  ring

theorem norm_vectorTerminalExponent_firstJet (β t : ℝ) (p : Couplings n × ℝ)
    (w x : Field n) (σ : Configuration n) :
    ‖iteratedFDeriv ℝ 1 (fun y => vectorTerminalExponent n β t p (y+w) σ) x‖=
      Real.sqrt (n : ℝ) := by
  rw [vectorTerminalExponent_eq_affine,norm_iteratedFDeriv_one,fderiv_const_add,
    ContinuousLinearMap.fderiv,innerSL_apply_norm,norm_spinVector]

theorem vectorTerminalExponent_higherJet_zero (β t : ℝ) (p : Couplings n × ℝ)
    (w x : Field n) (σ : Configuration n) (r : ℕ) (hr : 2 ≤ r) :
    iteratedFDeriv ℝ r (fun y => vectorTerminalExponent n β t p (y+w) σ) x=0 := by
  apply norm_eq_zero.mp
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  rw [←norm_iteratedFDeriv_fderiv,vectorTerminalExponent_eq_affine]
  have he : fderiv ℝ (fun y : Field n => vectorTerminalExponent n β t p w σ+
      innerSL ℝ (spinVector σ) y)=fun _ => innerSL ℝ (spinVector σ) := by
    funext y
    rw [fderiv_const_add,ContinuousLinearMap.fderiv]
  rw [he,iteratedFDeriv_const_of_ne (by omega : j ≠ 0)]
  simp

theorem norm_iteratedFDeriv_convex_sum_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {I : Type*} (S : Finset I) (a : I → ℝ) (f : I → E → ℝ)
    (r : ℕ) (B : ℝ) (hB : 0 ≤ B) (ha : ∀i ∈ S,0 ≤ a i)
    (hSum : ∑i ∈ S,a i ≤ 1) (hf : ∀i ∈ S,ContDiff ℝ ∞ (f i))
    (hb : ∀i ∈ S,∀x,‖iteratedFDeriv ℝ r (f i) x‖ ≤ B) (x : E) :
    ‖iteratedFDeriv ℝ r (fun y => ∑i ∈ S,a i*f i y) x‖ ≤ B := by
  rw [iteratedFDeriv_fun_sum_apply (fun i hi =>
    (contDiff_const.mul (hf i hi)).of_le (by simp) |>.contDiffAt)]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑i ∈ S,a i*B := Finset.sum_le_sum fun i hi => by
      rw [show (fun y => a i*f i y)=(fun y => a i • f i y) from rfl,
        iteratedFDeriv_const_smul_apply' ((hf i hi).of_le (by simp)).contDiffAt,norm_smul,
        Real.norm_eq_abs,abs_of_nonneg (ha i hi)]
      exact mul_le_mul_of_nonneg_left (hb i hi x) (ha i hi)
    _ = (∑i ∈ S,a i)*B := by rw [Finset.sum_mul]
    _ ≤ B := (mul_le_mul_of_nonneg_right hSum hB).trans_eq (one_mul _)

def vectorTailStieltjesWeight (s : RSBScheme k) (N : ℕ) : Option (Fin N) → ℝ
  | none => s.m (k+2-(N+1))
  | some i => s.m (k+2-(N+1)+(i+1))-s.m (k+2-(N+1)+i)

def vectorTailStieltjesPotential (s : RSBScheme k) (β t : ℝ) (p : Couplings n × ℝ)
    (N : ℕ) (z : Fin (N+1) → Field n) : Option (Fin N) → Field n → ℝ
  | none => fun x => vectorTailHistoryPotential s β t p x (N+1) 0 z
  | some i => fun x => vectorTailHistoryPotential s β t p x (N+1) (i+1) z

theorem vectorTailStieltjesWeight_nonneg (s : RSBScheme k) (N : ℕ)
    (hN : N+1 ≤ k+2) (i : Option (Fin N)) : 0 ≤ vectorTailStieltjesWeight s N i := by
  cases i with
  | none => exact s.m_nonneg (by omega)
  | some i =>
    apply sub_nonneg.mpr
    simpa only [Nat.add_assoc] using s.m_mono (k+2-(N+1)+i) (by omega)

theorem vectorTailStieltjesWeight_sum (s : RSBScheme k) (N : ℕ)
    (hN : N+1 ≤ k+2) : (∑i : Option (Fin N),vectorTailStieltjesWeight s N i)=1 := by
  rw [Fintype.sum_option]
  simp only [vectorTailStieltjesWeight]
  rw [Fin.sum_univ_eq_sum_range (fun i => s.m (k+2-(N+1)+(i+1))-s.m (k+2-(N+1)+i)) N]
  exact vectorTailStieltjesCoefficient_sum s N hN

theorem vectorTailLogDensity_stieltjes_sum (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (N : ℕ) (hN : N+1 ≤ k+2)
    (z : (Fin (N+1) → Field n) × Configuration n) :
    (fun x => vectorTailPosteriorLogDensity s β t p x (N+1) z)=
      fun x => vectorTerminalExponent n β t p
        (x+(vectorHistoryFrom s β t (k+2-(N+1)) p 0 (N+1) z.1 (Fin.last (N+1))).2) z.2-
        ∑i : Option (Fin N),vectorTailStieltjesWeight s N i*
          vectorTailStieltjesPotential s β t p N z.1 i x := by
  funext x
  rw [vectorTailPosteriorLogDensity_stieltjes s β t p x N hN,
    vectorHistoryFrom_field_eq_initial_add,Fintype.sum_option]
  simp only [vectorTailStieltjesWeight,vectorTailStieltjesPotential]
  rw [Fin.sum_univ_eq_sum_range (fun i =>
    (s.m (k+2-(N+1)+(i+1))-s.m (k+2-(N+1)+i))*
      vectorTailHistoryPotential s β t p x (N+1) (i+1) z.1) N]
  ring

theorem norm_vectorTailLogDensity_jet_le (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (r : ℕ) (A B : ℝ) (hB : 0 ≤ B)
    (hU : ∀j,j ≤ k+2 → ∀x,‖iteratedFDeriv ℝ r (vectorRecursion s β t p j) x‖ ≤ B)
    (hT : ∀w x σ,‖iteratedFDeriv ℝ r
      (fun y => vectorTerminalExponent n β t p (y+w) σ) x‖ ≤ A)
    (j : ℕ) (hj : j ≤ k+2) (x : Field n)
    (z : (Fin j → Field n) × Configuration n) :
    ‖iteratedFDeriv ℝ r (fun y => vectorTailPosteriorLogDensity s β t p y j z) x‖ ≤ A+B := by
  cases j with
  | zero =>
    have he : (fun y => vectorTailPosteriorLogDensity s β t p y 0 z)=
        fun y => vectorTerminalExponent n β t p (y+0) z.2-vectorRecursion s β t p 0 y := by
      funext y
      simp [vectorTailPosteriorLogDensity,vectorTailHistoryPotential_terminal,
        vectorHistoryFrom_initial,vectorRecursion]
    have hTs : ContDiff ℝ ∞ (fun y : Field n => vectorTerminalExponent n β t p (y+0) z.2) := by
      unfold vectorTerminalExponent fieldDot
      fun_prop
    rw [he]
    change ‖iteratedFDeriv ℝ r ((fun y => vectorTerminalExponent n β t p (y+0) z.2)-
      vectorRecursion s β t p 0) x‖ ≤ A+B
    rw [iteratedFDeriv_sub_apply (i := r) ((hTs.of_le (by simp)).contDiffAt)
      (((contDiff_vectorRecursion_field s β t p 0).of_le (by simp)).contDiffAt)]
    exact (norm_sub_le _ _).trans (add_le_add (hT 0 x z.2) (hU 0 (by omega) x))
  | succ N =>
    let w := (vectorHistoryFrom s β t (k+2-(N+1)) p 0 (N+1) z.1 (Fin.last (N+1))).2
    let U := vectorTailStieltjesPotential s β t p N z.1
    have hs (i : Option (Fin N)) : ContDiff ℝ ∞ (U i) := by
      cases i with
      | none =>
        change ContDiff ℝ ∞ (fun y => vectorTailHistoryPotential s β t p y (N+1) 0 z.1)
        rw [vectorTailHistoryPotential_eq_translate]
        exact (contDiff_vectorRecursion_field s β t p (N+1-0)).comp
          (contDiff_id.add contDiff_const)
      | some i =>
        change ContDiff ℝ ∞ (fun y => vectorTailHistoryPotential s β t p y (N+1) (i+1) z.1)
        rw [vectorTailHistoryPotential_eq_translate]
        exact (contDiff_vectorRecursion_field s β t p (N+1-(i+1))).comp
          (contDiff_id.add contDiff_const)
    have hb (i : Option (Fin N)) (y : Field n) : ‖iteratedFDeriv ℝ r (U i) y‖ ≤ B := by
      cases i with
      | none =>
        dsimp only [U,vectorTailStieltjesPotential]
        rw [vectorTailHistoryPotential_eq_translate,iteratedFDeriv_comp_add_right]
        exact hU _ (by omega) _
      | some i =>
        dsimp only [U,vectorTailStieltjesPotential]
        rw [vectorTailHistoryPotential_eq_translate,iteratedFDeriv_comp_add_right]
        exact hU _ (by omega) _
    have hsum := norm_iteratedFDeriv_convex_sum_le Finset.univ (vectorTailStieltjesWeight s N)
      U r B hB (fun i _ => vectorTailStieltjesWeight_nonneg s N hj i)
      (vectorTailStieltjesWeight_sum s N hj).le (fun i _ => hs i) (fun i _ => hb i) x
    have hTs : ContDiff ℝ ∞ (fun y : Field n => vectorTerminalExponent n β t p (y+w) z.2) := by
      unfold vectorTerminalExponent fieldDot
      fun_prop
    have hUs : ContDiff ℝ ∞ (fun y => ∑i : Option (Fin N),vectorTailStieltjesWeight s N i*U i y) :=
      ContDiff.sum fun i _ => contDiff_const.mul (hs i)
    rw [vectorTailLogDensity_stieltjes_sum s β t p N hj]
    change ‖iteratedFDeriv ℝ r ((fun y => vectorTerminalExponent n β t p (y+w) z.2)-
      (fun y => ∑i : Option (Fin N),vectorTailStieltjesWeight s N i*U i y)) x‖ ≤ A+B
    rw [iteratedFDeriv_sub_apply (i := r) ((hTs.of_le (by simp)).contDiffAt)
        ((hUs.of_le (by simp)).contDiffAt)]
    exact (norm_sub_le _ _).trans (add_le_add (hT w x z.2) hsum)

theorem norm_vectorTailLogDensity_firstJet_le (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (j : ℕ) (hj : j ≤ k+2) (x : Field n)
    (z : (Fin j → Field n) × Configuration n) :
    ‖iteratedFDeriv ℝ 1 (fun y => vectorTailPosteriorLogDensity s β t p y j z) x‖ ≤
      2*Real.sqrt (n : ℝ) := by
  simpa only [two_mul] using norm_vectorTailLogDensity_jet_le s β t p 1
    (Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ)) (Real.sqrt_nonneg _)
    (fun j _ => norm_vectorRecursion_firstJet_le s β t p j)
    (fun w x σ => (norm_vectorTerminalExponent_firstJet β t p w x σ).le) j hj x z

theorem norm_vectorTailLogDensity_secondJet_le (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (j : ℕ) (hj : j ≤ k+2) (x : Field n)
    (z : (Fin j → Field n) × Configuration n) :
    ‖iteratedFDeriv ℝ 2 (fun y => vectorTailPosteriorLogDensity s β t p y j z) x‖ ≤ (n : ℝ) := by
  simpa only [zero_add] using norm_vectorTailLogDensity_jet_le s β t p 2 0
    (n : ℝ) (Nat.cast_nonneg n)
    (fun j _ => norm_vectorRecursion_secondJet_le s β t p j)
    (fun w x σ => by rw [vectorTerminalExponent_higherJet_zero β t p w x σ 2 (by omega),norm_zero])
    j hj x z

end QuantitativePaper
