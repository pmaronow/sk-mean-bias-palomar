module
public import QuantitativePaper.VectorFiniteFutureCovariance
public import QuantitativePaper.VectorFiniteFutureTiltPairing

@[expose] public section

/-! Exact future covariance decomposition tested against the whole retained
Wiener past under the actual finite-profile fractional disorder law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon OverlapPaper
open scoped NNReal BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorFinite_future_covariance_pairing (s : RSBScheme k) (β t a : ℝ)
    (hβ : β ≠ 0) (ht : t < 1) (i : ℕ) (hi : i ≤ k+2) (w : Field n)
    (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (s.q i).toNNReal] Z)
    (C : ℝ≥0) (hC : ∀p, ‖Z p‖ ≤ C) :
    (∫p, Z p * inner ℝ w
      (vectorFieldHessian s β t p.1 (k+2-i)
        (vectorFiniteState s β t ht.le (s.q i).toNNReal p) w)
      ∂vectorFiniteDisorderTilt s β t a) =
      observableDepthMass s (k+2-i) *
        (∫p, Z p * vectorDepthCovariance s β t (fun σ => fieldDot w σ) (k+2-i)
          (vectorFiniteJointState s β t ht.le (s.q i).toNNReal p)
          ∂vectorFiniteDisorderTilt s β t a) +
      ∑u ∈ Finset.range (k+2-i),
        (observableDepthMass s u - observableDepthMass s (u+1)) *
          (∫p, Z p * vectorDepthCovariance s β t (fun σ => fieldDot w σ) u
            (vectorFiniteJointState s β t ht.le (s.q (k+2-u)).toNNReal p)
            ∂vectorFiniteDisorderTilt s β t a) := by
  let P := vectorFiniteDisorderTilt (n:=n) s β t a
  letI := vectorFiniteDisorderTilt_probability (n:=n) s β t a
  let R : ℝ≥0 := ⟨Real.sqrt (n:ℝ)*‖w‖, mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)⟩
  let b := fun σ : Configuration n => fieldDot w σ
  let j := k+2-i
  let X := fun p : VectorDisorderBrownianSample n =>
    vectorFiniteJointState s β t ht.le (s.q i).toNNReal p
  let F := fun u => sourceKernelExpectation (fun v => vectorDepthKernel s β t (u+v)) (j-u)
    (vectorDepthCovariance s β t b u)
  let d := fun u => observableDepthMass s u - observableDepthMass s (u+1)
  have hb σ : |b σ| ≤ R := abs_fieldDot w σ
  have hZm : Measurable Z := hZ.mono ((vectorBrownianFiltration n).le _) le_rfl
  have hXm : Measurable X := measurable_vectorFiniteJointState s β t ht.le _
  have hFm u : Measurable (F u) :=
    sourceKernelExpectation_measurable _ _ (measurable_vectorDepthCovariance s β t b u) _
  have hFb u x : |F u x| ≤ (R:ℝ)^2 :=
    sourceKernelExpectation_abs_le _ (fun _ => inferInstance) _
      (measurable_vectorDepthCovariance s β t b u) _ (sq_nonneg _)
      (vectorDepthCovariance_abs_le s β t b R hb u) _ x
  have hZFp u : Integrable (fun p => Z p*F u (X p)) P :=
    source_bounded_integrable P _ (hZm.mul ((hFm u).comp hXm)) ((C:ℝ)*(R:ℝ)^2)
      (fun p => by
        rw [abs_mul]
        exact mul_le_mul (by simpa only [Real.norm_eq_abs] using hC p) (hFb u (X p))
          (abs_nonneg _) C.coe_nonneg)
  have hZF u : Integrable (fun p => d u*(Z p*F u (X p))) P := (hZFp u).const_mul _
  have hcurrent : Integrable (fun p => Z p*vectorDepthCovariance s β t b j (X p)) P :=
    source_bounded_integrable P _
      (hZm.mul ((measurable_vectorDepthCovariance s β t b j).comp hXm)) ((C:ℝ)*(R:ℝ)^2)
      (fun p => by
        rw [abs_mul]
        exact mul_le_mul (by simpa only [Real.norm_eq_abs] using hC p)
          (vectorDepthCovariance_abs_le s β t b R hb j (X p)) (abs_nonneg _) C.coe_nonneg)
  have he : (fun p : VectorDisorderBrownianSample n => Z p*inner ℝ w
      (vectorFieldHessian s β t p.1 j (vectorFiniteState s β t ht.le (s.q i).toNNReal p) w)) =
      fun p => observableDepthMass s j*(Z p*vectorDepthCovariance s β t b j (X p)) +
        ∑u ∈ Finset.range j, d u*(Z p*F u (X p)) := by
    funext p
    rw [vectorFieldHessian_future_covariance_sum]
    change Z p*(observableDepthMass s j*vectorDepthCovariance s β t b j (X p) +
      ∑u ∈ Finset.range j, d u*F u (X p)) = _
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro u _
      ring
  change (∫p, Z p*inner ℝ w
    (vectorFieldHessian s β t p.1 j (vectorFiniteState s β t ht.le (s.q i).toNNReal p) w) ∂P) = _
  rw [he, integral_add (hcurrent.const_mul _) (integrable_finsetSum _ (fun u _ => hZF u)),
    integral_const_mul, integral_finsetSum _ (fun u _ => hZF u)]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  rw [integral_const_mul]
  congr 1
  have hiu : i ≤ k+2-u := by have := Finset.mem_range.mp hu; dsimp [j] at this; omega
  have huu : k+2-u ≤ k+2 := Nat.sub_le _ _
  have hp : k+2-(k+2-u)=u := by have := Finset.mem_range.mp hu; dsimp [j] at this; omega
  have hq : k+2-u-i=j-u := by dsimp [j]; omega
  have hpast := vectorFinite_future_weighted_pairing_tilt s β t a hβ ht i (k+2-u) hiu huu
    (vectorDepthCovariance s β t b u) (measurable_vectorDepthCovariance s β t b u) ((R:ℝ)^2)
    (fun x => by simpa only [Real.norm_eq_abs] using vectorDepthCovariance_abs_le s β t b R hb u x)
    Z hZ C hC
  symm
  simpa only [vectorFiniteFutureExpectation, hp, hq, F, X, P] using hpast

end QuantitativePaper
