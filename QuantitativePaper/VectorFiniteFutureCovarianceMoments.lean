module
public import QuantitativePaper.VectorFiniteFutureCovariancePairing
public import QuantitativePaper.VectorFinitePastSpinPairing

@[expose] public section

/-! Every finite future covariance has its actual terminal-second-moment
minus future-mean-square pairing, for tests of any earlier whole past. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon OverlapPaper
open scoped NNReal BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorFinite_future_covariance_moment_pairing (s : RSBScheme k) (β t a : ℝ)
    (hβ : β ≠ 0) (ht : t < 1) (i u : ℕ) (hiu : i ≤ u) (hu : u ≤ k+2)
    (b : Configuration n → ℝ) (R : ℝ≥0) (hb : ∀σ, |b σ| ≤ R)
    (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (s.q i).toNNReal] Z)
    (C : ℝ≥0) (hC : ∀p, ‖Z p‖ ≤ C) :
    (∫p, Z p*vectorDepthCovariance s β t b (k+2-u)
      (vectorFiniteJointState s β t ht.le (s.q u).toNNReal p)
      ∂vectorFiniteDisorderTilt s β t a) =
      (∫p, Z p*terminalMean (vectorTerminalExponent n β t p.1
        (vectorFiniteState s β t ht.le 1 p)) (fun σ => b σ^2)
        ∂vectorFiniteDisorderTilt s β t a) -
      ∫p, Z p*(vectorBackwardMean s β t b u
        (vectorFiniteJointState s β t ht.le (s.q u).toNNReal p))^2
        ∂vectorFiniteDisorderTilt s β t a := by
  let P := vectorFiniteDisorderTilt (n:=n) s β t a
  letI := vectorFiniteDisorderTilt_probability (n:=n) s β t a
  let X := fun p : VectorDisorderBrownianSample n =>
    vectorFiniteJointState s β t ht.le (s.q u).toNNReal p
  have hZm : Measurable Z := hZ.mono ((vectorBrownianFiltration n).le _) le_rfl
  have hXm : Measurable X := measurable_vectorFiniteJointState s β t ht.le _
  have hb2 σ : |b σ^2| ≤ (R:ℝ)^2 := by
    rw [abs_sq]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (b σ)) (hb σ) 2
  have hB σ : |b σ| ≤ (R:ℝ) := hb σ
  have hiB : Integrable (fun p => Z p*vectorBackwardMean s β t (fun σ => b σ^2) u (X p)) P :=
    source_bounded_integrable P _
      (hZm.mul ((measurable_vectorBackwardMean s β t _ u).comp hXm)) ((C:ℝ)*(R:ℝ)^2)
      (fun p => by
        rw [abs_mul]
        exact mul_le_mul (by simpa only [Real.norm_eq_abs] using hC p)
          (abs_vectorBackwardMean_le s β t _ _ hb2 u (X p)) (abs_nonneg _) C.coe_nonneg)
  have hiM : Integrable (fun p => Z p*(vectorBackwardMean s β t b u (X p))^2) P :=
    source_bounded_integrable P _
      (hZm.mul (((measurable_vectorBackwardMean s β t b u).comp hXm).pow_const 2))
      ((C:ℝ)*(R:ℝ)^2) (fun p => by
        rw [abs_mul, abs_sq]
        exact mul_le_mul (by simpa only [Real.norm_eq_abs] using hC p)
          (by simpa only [sq_abs] using (pow_le_pow_left₀
            (abs_nonneg (vectorBackwardMean s β t b u (X p)))
            (abs_vectorBackwardMean_le s β t b R hB u (X p)) 2))
          (sq_nonneg _) C.coe_nonneg)
  have hcov : (fun p : VectorDisorderBrownianSample n => Z p*vectorDepthCovariance s β t b (k+2-u) (X p)) =
      fun p => Z p*vectorBackwardMean s β t (fun σ => b σ^2) u (X p) -
        Z p*(vectorBackwardMean s β t b u (X p))^2 := by
    funext p
    rw [show vectorDepthCovariance s β t b (k+2-u) (X p) = vectorBackwardVariance s β t b u (X p) from
      (vectorBackwardVariance_eq_observableCovariance s β t b u (X p)).symm]
    unfold vectorBackwardVariance
    ring
  rw [hcov, integral_sub hiB hiM]
  have hZu : Measurable[vectorBrownianFiltration n (s.q u).toNNReal] Z :=
    hZ.mono ((vectorBrownianFiltration n).mono (Real.toNNReal_mono
      (s.q_mono' u hu i hiu))) le_rfl
  rw [←vectorFinite_terminal_mean_pairing_past s β t a hβ ht (fun σ => b σ^2) u hu Z hZu C hC]

theorem vectorDepthMass_future_telescope (s : RSBScheme k) (j : ℕ) :
    (∑u ∈ Finset.range j, (observableDepthMass s u - observableDepthMass s (u+1))) =
      1-observableDepthMass s j := by
  induction j with
  | zero => simp [observableDepthMass]
  | succ j ih => rw [Finset.sum_range_succ, ih]; ring

end QuantitativePaper
