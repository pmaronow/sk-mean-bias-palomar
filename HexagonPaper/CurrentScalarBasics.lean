module
public import QuantitativeFollowup.SupportingScalarPrintedRecursiveBound
public import HexagonPaper.VariancePressureScalarJetTimeBounds

@[expose] public section

/-! Current-paper scalar basic regularity, uniform in the entire variance
window. The constants below are obtained from the proved recursive jet
bounds, rather than from a separate fixed-temperature compactness selector.
No minimizing-profile assumption is used. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper FRSB QuantitativeFollowup
open scoped Topology NNReal BigOperators BoundedContinuousFunction
namespace HexagonPaper
open SpinGlass.Targets
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

private theorem currentScalarJetNorm_zero (γ : ℝ) (μ : Paper.ParisiMeasure) :
    scalarPrintedPositiveJetNorm γ μ 0 ≤ 1 := by
  simpa only [scalarPrintedPositiveJetNorm, bcfSpatialDerivative,
    iteratedDeriv_zero, bcfTranslate_zero] using norm_parisiGradientBCF_le_one γ μ

private theorem currentScalarJetNorm_one (γ : ℝ) (μ : Paper.ParisiMeasure) :
    scalarPrintedPositiveJetNorm γ μ 1 ≤ 1 := by
  apply (BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro p
  have he : parisiSpatialJet γ μ 2 (p.1 : ℝ) p.2 =
      bcfSpatialDerivative (parisiGradientBCF γ μ) 1 p := by
    simp only [parisiSpatialJet, show (2 : ℕ) ≠ 0 by omega, ite_false,
      show (2 : ℕ)-1=1 by omega, parisiSlabExtend]
    rw [projIcc_of_mem _ p.1.property]
  rw [← he, parisiSpatialJet_two]
  exact norm_parisiHessian_le_one_all γ μ _

private theorem currentScalarTerminalJetSlice (γ γ' : ℝ)
    (μ μ' : Paper.ParisiMeasure) (r : ℕ) :
    scalarPrintedJetSlice γ μ r 1 = scalarPrintedJetSlice γ' μ' r 1 := by
  ext x
  rw [scalarPrintedJetSlice_terminal_log_two_cosh,
    scalarPrintedJetSlice_terminal_log_two_cosh]

/-- One finite constant bounds every native gradient jet of order at most `n`,
uniformly over all probability profiles and the whole variance window. -/
theorem currentScalarFiniteJetNormBound (β : ℝ) (hβ : 0 < β) (n : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (d : ℝ), d ∈ Icc (β^2/2) (β^2) →
      ∀ (μ : Paper.ParisiMeasure) (r : ℕ), r ≤ n →
        scalarPrintedPositiveJetNorm (Real.sqrt d) μ r ≤ K := by
  induction n with
  | zero =>
      refine ⟨1, le_refl _, fun d hd μ r hr => ?_⟩
      have hr0 : r = 0 := by omega
      subst r
      exact currentScalarJetNorm_zero _ _
  | succ n hn =>
      obtain ⟨K, hK, hbound⟩ := hn
      by_cases hn0 : n = 0
      · subst n
        refine ⟨1, le_refl _, fun d hd μ r hr => ?_⟩
        rcases (by omega : r = 0 ∨ r = 1) with hr0 | hr1
        · subst r; exact currentScalarJetNorm_zero _ _
        · subst r; exact currentScalarJetNorm_one _ _
      · let μ₀ : Paper.ParisiMeasure := diracOverlap 0 (by simp)
        let T : ℝ := ‖scalarPrintedJetSlice β μ₀ (n+1) 1‖
        let S : ℝ := ∑ i ∈ Finset.Icc 2 n,
          ((n+2).choose i : ℝ) * K * K
        let A : ℝ := Real.exp ((n+2 : ℕ) * β^2) * (T + β^2/2*S)
        refine ⟨max K A, hK.trans (le_max_left _ _), fun d hd μ r hr => ?_⟩
        by_cases hrn : r ≤ n
        · exact (hbound d hd μ r hrn).trans (le_max_left _ _)
        · have hr1 : r = n+1 := by omega
          subst r
          have hp := scalarPrintedHigherJet_recursive_variance_window β d hβ hd μ
            (n+2) (by omega)
          have hterm := currentScalarTerminalJetSlice (Real.sqrt d) β μ μ₀ (n+1)
          have hsum : (∑ i ∈ Finset.Icc 2 n, ((n+2).choose i : ℝ) *
              scalarPrintedPositiveJetNorm (Real.sqrt d) μ i *
              scalarPrintedPositiveJetNorm (Real.sqrt d) μ (n+2-i)) ≤ S := by
            apply Finset.sum_le_sum
            intro i hi
            obtain ⟨hi0, hi1⟩ := Finset.mem_Icc.mp hi
            have hi2 : n+2-i ≤ n := by omega
            apply mul_le_mul
              (mul_le_mul_of_nonneg_left (hbound d hd μ i hi1) (Nat.cast_nonneg _))
              (hbound d hd μ (n+2-i) hi2)
              (by unfold scalarPrintedPositiveJetNorm; positivity)
              (mul_nonneg (Nat.cast_nonneg _) (by linarith))
          rw [show (n+2)-1=n+1 by omega, show (n+2)-2=n by omega, hterm] at hp
          have hA : scalarPrintedPositiveJetNorm (Real.sqrt d) μ (n+1) ≤ A := by
            apply hp.trans
            exact mul_le_mul_of_nonneg_left
              (add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum (by positivity)))
              (Real.exp_pos _).le
          exact hA.trans (le_max_right _ _)

/-- The positive-order spatial derivative clause of current `lem:sc-basic`. -/
theorem currentScalarPositiveSpatialJetBound (β : ℝ) (hβ : 0 < β)
    (j : ℕ) (hj : 1 ≤ j) :
    ∃ K : ℝ, 0 < K ∧ ∀ (d : ℝ), d ∈ Icc (β^2/2) (β^2) →
      ∀ (μ : Paper.ParisiMeasure) (q x : ℝ), q ∈ Icc (0 : ℝ) 1 →
        ‖iteratedDeriv j (fun y => parisiPotential (Real.sqrt d) μ (q,y)) x‖ ≤ K := by
  obtain ⟨K, hK, hbound⟩ := currentScalarFiniteJetNormBound β hβ (j-1)
  refine ⟨K, lt_of_lt_of_le zero_lt_one hK, fun d hd μ q x hq => ?_⟩
  rw [← parisiSpatialJet_eq_iteratedDeriv (Real.sqrt d) μ j q x hq]
  have hb := norm_parisiSpatialJet_succ_le (Real.sqrt d) μ (j-1) q x
  rw [Nat.sub_add_cancel hj] at hb
  exact hb.trans (hbound d hd μ (j-1) le_rfl)

private theorem currentScalarForcingBound (β d K : ℝ) (hd : d ∈ Icc (β^2/2) (β^2))
    (hK : 0 ≤ K)
    (hbound : ∀ (μ : Paper.ParisiMeasure) (r : ℕ), r ≤ 3 →
      scalarPrintedPositiveJetNorm (Real.sqrt d) μ r ≤ K)
    (μ : Paper.ParisiMeasure) (m : ℝ) (hm : m ∈ Icc (0 : ℝ) 1) (t x : ℝ) :
    ‖cellTimeForcing (Real.sqrt d) μ m 2 t x‖ ≤ β^2/2*(K+4*K*K) := by
  have hd0 : 0 ≤ d := (by positivity : 0 ≤ β^2/2).trans hd.1
  have hsq : (Real.sqrt d)^2 = d := Real.sq_sqrt hd0
  have hb (r : ℕ) (hr : r ≤ 3) :
      ‖parisiSpatialJet (Real.sqrt d) μ (r+1) t x‖ ≤ K :=
    (norm_parisiSpatialJet_succ_le _ _ _ _ _).trans (hbound μ r hr)
  have hsum : ‖∑ k ∈ Finset.range 3, ((2 : ℕ).choose k : ℝ)*
      parisiSpatialJet (Real.sqrt d) μ (k+1) t x*
      parisiSpatialJet (Real.sqrt d) μ (2-k+1) t x‖ ≤ 4*K*K := by
    apply (norm_sum_le _ _).trans
    have hs : (∑ k ∈ Finset.range 3, ((2 : ℕ).choose k : ℝ)*
        ‖parisiSpatialJet (Real.sqrt d) μ (k+1) t x‖*
        ‖parisiSpatialJet (Real.sqrt d) μ (2-k+1) t x‖) ≤
        ∑ k ∈ Finset.range 3, ((2 : ℕ).choose k : ℝ)*K*K := by
      apply Finset.sum_le_sum
      intro k hk
      have hk3 : k < 3 := Finset.mem_range.mp hk
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hb k (by omega))
        (Nat.cast_nonneg _)) (hb (2-k) (by omega)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hK)
    simp only [norm_mul, Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact hs.trans_eq (by norm_num [Finset.sum_range_succ]; ring)
  rw [cellTimeForcing_eq, norm_mul, norm_neg, hsq,
    Real.norm_of_nonneg (by positivity : 0 ≤ d/2)]
  have hinside : ‖parisiSpatialJet (Real.sqrt d) μ 4 t x + m *
      ∑ k ∈ Finset.range 3, ((2 : ℕ).choose k : ℝ)*
        parisiSpatialJet (Real.sqrt d) μ (k+1) t x*
        parisiSpatialJet (Real.sqrt d) μ (2-k+1) t x‖ ≤ K+4*K*K := by
    apply (norm_add_le _ _).trans
    apply add_le_add (hb 3 (by omega))
    rw [norm_mul, Real.norm_of_nonneg hm.1]
    exact (mul_le_mul_of_nonneg_right hm.2 (norm_nonneg _)).trans
      (by simpa only [one_mul] using hsum)
  exact mul_le_mul (by linarith [hd.2] : d/2 ≤ β^2/2) hinside
    (norm_nonneg _) (by positivity)

private theorem currentScalarFiniteCellTimeBound (γ C : ℝ) (hγ : γ ≠ 0)
    (hforcing : ∀ (μ : Paper.ParisiMeasure) (m : ℝ), m ∈ Icc (0 : ℝ) 1 →
      ∀ t x, ‖cellTimeForcing γ μ m 2 t x‖ ≤ C)
    {k : ℕ} (s : RSBScheme k) {p : ℕ} (hp : p ≤ k+1)
    (hq : s.q p < s.q (p+1)) {l r : ℝ} (hl : s.q p ≤ l)
    (hlr : l ≤ r) (hr : r ≤ s.q (p+1)) (x : ℝ) :
    ‖parisiSpatialJet γ (parisiSchemeMeasure s) 2 r x-
      parisiSpatialJet γ (parisiSchemeMeasure s) 2 l x‖ ≤ C*(r-l) := by
  have hh := closed_interval_increment_bound
    (fun t => parisiSpatialJet γ (parisiSchemeMeasure s) 2 t x) (fun _ => 0)
    (fun _ => C)
    ((continuous_parisiSpatialJet_succ γ (parisiSchemeMeasure s) 1).comp
      (continuous_id.prodMk continuous_const))
    (fun _ _ => intervalIntegrable_const) (fun _ _ => intervalIntegrable_const) hq
    (by
      intro a b ha hab hb
      have hder (t : ℝ) (ht : t ∈ Icc a b) :=
        hasDerivAt_finiteCell_spatialJet_time s γ hγ hp hq 2
          ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩ x
      have hm : s.m p ∈ Icc (0 : ℝ) 1 := ⟨s.m_nonneg (by omega), s.m_le_one (by omega)⟩
      have hinc := Convex.norm_image_sub_le_of_norm_deriv_le (C:=C)
        (fun t ht => (hder t ht).differentiableAt)
        (fun t ht => by rw [(hder t ht).deriv]; exact hforcing _ _ hm t x)
        (convex_Icc a b) (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
      simpa only [intervalIntegral.integral_zero, sub_zero, intervalIntegral.integral_const,
        smul_eq_mul, Real.norm_of_nonneg (sub_nonneg.mpr hab), mul_comm] using hinc)
    hl hlr hr
  simpa only [intervalIntegral.integral_zero, sub_zero, intervalIntegral.integral_const,
    smul_eq_mul, mul_comm] using hh

private theorem currentScalarGridTimeBound (γ C : ℝ) (hγ : γ ≠ 0)
    (hforcing : ∀ (μ : Paper.ParisiMeasure) (m : ℝ), m ∈ Icc (0 : ℝ) 1 →
      ∀ t x, ‖cellTimeForcing γ μ m 2 t x‖ ≤ C)
    (μ : Paper.ParisiMeasure) (n : ℕ) {r t : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hrt : r ≤ t) (x : ℝ) :
    ‖parisiSpatialJet γ (parisiGridMeasure μ n) 2 t x-
      parisiSpatialJet γ (parisiGridMeasure μ n) 2 r x‖ ≤ C*(t-r) := by
  let T := fun i => min t (max r (hjbGridTime n i))
  let F := fun i => parisiSpatialJet γ (parisiGridMeasure μ n) 2 (T i) x
  have hgrid : Monotone (hjbGridTime n) := by
    intro i j hij
    exact div_le_div_of_nonneg_right (by exact_mod_cast hij) (by positivity)
  have hTmono : Monotone T := monotone_const.min (monotone_const.max hgrid)
  have htel := parisiGradientMesh_norm_telescope F (fun _ => C) T (n+1)
    (fun _ _ => intervalIntegrable_const) (by
      intro i hi
      by_cases he : T i = T (i+1)
      · simp only [F, he, sub_self, intervalIntegral.integral_same, norm_zero, le_refl]
      · have hlt : T i < T (i+1) := lt_of_le_of_ne (hTmono (Nat.le_succ i)) he
        have hir : r < hjbGridTime n (i+1) := by
          by_contra hh
          have hmax0 : max r (hjbGridTime n i) = r := max_eq_left
            ((hgrid (Nat.le_succ i)).trans (le_of_not_gt hh))
          have hmax1 : max r (hjbGridTime n (i+1)) = r := max_eq_left (le_of_not_gt hh)
          exact he (by simp only [T, hmax0, hmax1])
        have hit : hjbGridTime n i < t := by
          by_contra hh
          have hmin0 : min t (max r (hjbGridTime n i)) = t := min_eq_left
            ((le_of_not_gt hh).trans (le_max_right _ _))
          have hmin1 : min t (max r (hjbGridTime n (i+1))) = t := min_eq_left
            (((le_of_not_gt hh).trans (hgrid (Nat.le_succ i))).trans (le_max_right _ _))
          exact he (by simp only [T, hmin0, hmin1])
        have ha : hjbGridTime n i ≤ T i := le_min hit.le (le_max_right _ _)
        have hb : T (i+1) ≤ hjbGridTime n (i+1) := by
          dsimp only [T]
          rw [max_eq_right hir.le]
          exact min_le_right _ _
        let s := parisiGridRSBScheme μ n
        obtain ⟨hq0, hq1⟩ := hjbGrid_cell_q μ n i hi
        have hq : s.q (i+1) < s.q (i+1+1) := by
          simpa only [s, hq0, show i+1+1=i+2 by omega, hq1] using hjbGridTime_step_lt n i
        have hh := currentScalarFiniteCellTimeBound γ C hγ hforcing s (p:=i+1) (by omega) hq
          (by simpa only [s, hq0] using ha) hlt.le
          (by simpa only [s, show i+1+1=i+2 by omega, hq1] using hb) x
        rw [parisiSchemeMeasure_grid_eq μ n] at hh
        simpa only [F, intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hh)
  have hg0 : hjbGridTime n 0 = 0 := by simp [hjbGridTime]
  have hg1 : hjbGridTime n (n+1) = 1 := by
    unfold hjbGridTime
    exact div_self (by positivity)
  have h0 : T 0 = r := by simp only [T, hg0, max_eq_left hr.1, min_eq_right hrt]
  have h1 : T (n+1) = t := by simp only [T, hg1, max_eq_right hr.2, min_eq_left ht.2]
  simpa only [F, h0, h1, intervalIntegral.integral_const, smul_eq_mul, mul_comm] using htel

/-- Uniform time Lipschitz regularity of the current paper's scalar Hessian,
including CDF atom times. -/
theorem currentScalarHessianTimeLipschitz (β : ℝ) (hβ : 0 < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : ℝ), d ∈ Icc (β^2/2) (β^2) →
      ∀ (μ : Paper.ParisiMeasure) (r t : ℝ), r ∈ Icc (0 : ℝ) 1 →
        t ∈ Icc (0 : ℝ) 1 → ∀ x,
          ‖parisiHessian (Real.sqrt d) μ (t,x)-parisiHessian (Real.sqrt d) μ (r,x)‖ ≤
            C*‖t-r‖ := by
  obtain ⟨K, hK, hbound⟩ := currentScalarFiniteJetNormBound β hβ 3
  let C := β^2/2*(K+4*K*K)
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  refine ⟨C, by dsimp only [C]; positivity, fun d hd μ r t hr ht x => ?_⟩
  have hdpos : 0 < d := lt_of_lt_of_le (by positivity : 0 < β^2/2) hd.1
  have hroot : Real.sqrt d ≠ 0 := (Real.sqrt_pos.mpr hdpos).ne'
  have hforcing : ∀ (ν : Paper.ParisiMeasure) (m : ℝ), m ∈ Icc (0 : ℝ) 1 →
      ∀ v y, ‖cellTimeForcing (Real.sqrt d) ν m 2 v y‖ ≤ C :=
    currentScalarForcingBound β d K hd hK0 (hbound d hd)
  have hordered {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
      (hab : a ≤ b) :
      ‖parisiSpatialJet (Real.sqrt d) μ 2 b x-parisiSpatialJet (Real.sqrt d) μ 2 a x‖ ≤
        C*‖b-a‖ := by
    have hh := le_of_tendsto
      (((nativeSpatialJet_grid_tendsto (Real.sqrt d) μ 1 b x hb).sub
        (nativeSpatialJet_grid_tendsto (Real.sqrt d) μ 1 a x ha)).norm)
      (.of_forall fun n => currentScalarGridTimeBound (Real.sqrt d) C hroot hforcing
        μ n ha hb hab x)
    simpa only [Real.norm_of_nonneg (sub_nonneg.mpr hab)] using hh
  simp only [← parisiSpatialJet_two]
  by_cases hrt : r ≤ t
  · exact hordered hr ht hrt
  · simpa only [norm_sub_rev] using hordered ht hr (le_of_not_ge hrt)

end HexagonPaper
