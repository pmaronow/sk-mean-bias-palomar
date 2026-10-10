module
public import QuantitativePaper.VectorFiniteFutureCovarianceMoments

@[expose] public section

/-! Exact finite Hessian identity in terms of actual terminal second
moments and future magnetization squares. This form passes to continuous
profile limits without choosing a jointly measurable covariance version. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon OverlapPaper
open scoped NNReal BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorFinite_future_mean_loss (s : RSBScheme k) (β t a : ℝ)
    (hβ : β ≠ 0) (ht : t < 1) (i : ℕ) (hi : i ≤ k+2) (w : Field n)
    (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (s.q i).toNNReal] Z)
    (C : ℝ≥0) (hC : ∀p, ‖Z p‖ ≤ C) :
    (∫p, Z p * inner ℝ w
      (vectorFieldHessian s β t p.1 (k+2-i)
        (vectorFiniteState s β t ht.le (s.q i).toNNReal p) w)
      ∂vectorFiniteDisorderTilt s β t a) +
      observableDepthMass s (k+2-i) *
        (∫p, Z p*(vectorBackwardMean s β t (fun σ => fieldDot w σ) i
          (vectorFiniteJointState s β t ht.le (s.q i).toNNReal p))^2
          ∂vectorFiniteDisorderTilt s β t a) +
      (∑u ∈ Finset.range (k+2-i),
        (observableDepthMass s u - observableDepthMass s (u+1)) *
          (∫p, Z p*(vectorBackwardMean s β t (fun σ => fieldDot w σ) (k+2-u)
            (vectorFiniteJointState s β t ht.le (s.q (k+2-u)).toNNReal p))^2
            ∂vectorFiniteDisorderTilt s β t a)) =
      ∫p, Z p*terminalMean (vectorTerminalExponent n β t p.1
        (vectorFiniteState s β t ht.le 1 p)) (fun σ => (fieldDot w σ)^2)
        ∂vectorFiniteDisorderTilt s β t a := by
  let P := vectorFiniteDisorderTilt (n:=n) s β t a
  let R : ℝ≥0 := ⟨Real.sqrt (n:ℝ)*‖w‖, mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)⟩
  let b := fun σ : Configuration n => fieldDot w σ
  let j := k+2-i
  let T := ∫p : VectorDisorderBrownianSample n, Z p*terminalMean
    (vectorTerminalExponent n β t p.1 (vectorFiniteState s β t ht.le 1 p))
    (fun σ => b σ^2) ∂P
  let M := fun u => ∫p : VectorDisorderBrownianSample n,
    Z p*(vectorBackwardMean s β t b (k+2-u)
      (vectorFiniteJointState s β t ht.le (s.q (k+2-u)).toNNReal p))^2 ∂P
  let D := fun u => ∫p : VectorDisorderBrownianSample n, Z p*vectorDepthCovariance s β t b u
    (vectorFiniteJointState s β t ht.le (s.q (k+2-u)).toNNReal p) ∂P
  let d := fun u => observableDepthMass s u - observableDepthMass s (u+1)
  have hb σ : |b σ| ≤ R := abs_fieldDot w σ
  have hcur := vectorFinite_future_covariance_moment_pairing s β t a hβ ht i i le_rfl hi b R hb Z hZ C hC
  have hfuture (u : ℕ) (hu : u ∈ Finset.range j) : D u = T-M u := by
    have hiu : i ≤ k+2-u := by have := Finset.mem_range.mp hu; dsimp [j] at this; omega
    have hku : k+2-(k+2-u)=u := by have := Finset.mem_range.mp hu; dsimp [j] at this; omega
    simpa only [hku, D, T, M, P] using
      vectorFinite_future_covariance_moment_pairing s β t a hβ ht i (k+2-u) hiu
        (Nat.sub_le _ _) b R hb Z hZ C hC
  have hsum : (∑u ∈ Finset.range j, d u*D u) =
      (1-observableDepthMass s j)*T - ∑u ∈ Finset.range j, d u*M u := by
    calc
      _ = ∑u ∈ Finset.range j, d u*(T-M u) := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [hfuture u hu]
      _ = (∑u ∈ Finset.range j, d u)*T - ∑u ∈ Finset.range j, d u*M u := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib, ←Finset.sum_mul]
      _ = _ := by rw [vectorDepthMass_future_telescope]
  have hc := vectorFinite_future_covariance_pairing s β t a hβ ht i hi w Z hZ C hC
  rw [hcur] at hc
  change _ = observableDepthMass s j*(T-_) + ∑u ∈ Finset.range j, d u*D u at hc
  rw [hsum] at hc
  change _ + observableDepthMass s j*_ + ∑u ∈ Finset.range j, d u*M u = T
  nlinarith [hc]

end QuantitativePaper
